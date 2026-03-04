/**
 * Singleton message router: holds Web Worker reference, sends JSON-RPC to worker,
 * routes worker messages (LSP responses and custom notifications) to store and client.
 */

import {
  WORKER_MSG_READY,
  WORKER_MSG_ERROR,
  WORKER_MSG_INIT,
  WORKER_MSG_CREATE_STREAM_RESPONSE,
  CREATE_STREAM_INPUT_TIMEOUT_MS,
} from '~/lib/constants'
import { routeMessage } from './route-message'

let worker: Worker | null = null
let workerReady = false
let readyResolve: (() => void) | null = null
let readyReject: ((reason: unknown) => void) | null = null
const readyPromise = new Promise<void>((resolve, reject) => {
  readyResolve = resolve
  readyReject = reject
})

/** Callback to push raw LSP JSON-RPC messages to the language client reader (e.g. for createMessageConnection). */
let incomingLspPush: ((raw: string) => void) | null = null
/** Response IDs already delivered to the connection (avoid duplicate/error overwriting a prior result). */
const deliveredResponseIds = new Set<string | number>()

export function getWorker(): Worker | null {
  return worker
}

export function isWorkerReady(): boolean {
  return workerReady
}

/**
 * Returns a Promise that resolves when the worker has posted WORKER_MSG_READY.
 * Resolves immediately if isWorkerReady() is already true.
 */
export function waitForWorkerReady(): Promise<void> {
  if (workerReady) return Promise.resolve()
  return readyPromise
}

/** Set callback to receive every incoming LSP message (after routeMessage). Used by the language connection. */
export function setIncomingLspPush(cb: ((raw: string) => void) | null): void {
  incomingLspPush = cb
}

/** Reset workerReady and pending stream resolvers for test isolation. Do not use in production. */
export function resetMessageRouterForTest(): void {
  workerReady = false
  for (const [, entry] of pendingStreamResolvers) {
    clearTimeout(entry.timeoutId)
    entry.reject(new Error('Message router reset'))
  }
  pendingStreamResolvers.clear()
}

/** Set worker instance for tests (e.g. mock worker). Do not use in production. */
export function setWorkerForTest(w: Worker | null): void {
  worker = w
}

/**
 * Process an incoming worker message. If it is a control message (ready or error),
 * updates workerReady and returns true (caller should not pass to routeMessage).
 * Otherwise returns false and the caller should pass the raw string to routeMessage.
 */
interface PendingStreamResolver {
  resolve: (index: number) => void
  reject: (err: Error) => void
  timeoutId: ReturnType<typeof setTimeout>
}
const pendingStreamResolvers = new Map<number, PendingStreamResolver>()

export function processIncomingWorkerMessage(data: string): boolean {
  try {
    const parsed = JSON.parse(data) as {
      type?: string
      error?: string
      id?: number
      index?: number
    }
    if (parsed && typeof parsed.type === 'string') {
      if (parsed.type === WORKER_MSG_READY) {
        workerReady = true
        if (readyResolve) {
          readyResolve()
          readyResolve = null
        }
        return true
      }
      if (parsed.type === WORKER_MSG_ERROR) {
        workerReady = false
        const errMsg = parsed.error ?? 'Unknown error'
        console.error('[LSP Worker]', errMsg)
        if (typeof window !== 'undefined') {
          ;(window as unknown as { __E2E_LSP_WORKER_ERROR__?: string }).__E2E_LSP_WORKER_ERROR__ = errMsg
        }
        if (readyReject) {
          readyReject(new Error(errMsg))
          readyReject = null
        }
        return true
      }
      if (parsed.type === WORKER_MSG_CREATE_STREAM_RESPONSE && typeof parsed.id === 'number') {
        const entry = pendingStreamResolvers.get(parsed.id)
        pendingStreamResolvers.delete(parsed.id)
        if (entry) {
          clearTimeout(entry.timeoutId)
          if (typeof parsed.error === 'string') {
            entry.reject(new Error(parsed.error))
          } else if (typeof parsed.index === 'number') {
            entry.resolve(parsed.index)
          } else {
            entry.reject(new Error('Invalid createStreamInput response'))
          }
        }
        return true
      }
    }
  } catch {
    // not JSON or not a control message
  }
  return false
}

const LSP_HEADER_RE = /Content-Length:\s*(\d+)\s*\r?\n\r?\n/s

/**
 * Strip one LSP Content-Length frame from the start; returns the JSON body and any remainder.
 */
function takeOneLspFrame(raw: string): { body: string; rest: string } {
  const match = LSP_HEADER_RE.exec(raw)
  if (!match) return { body: raw, rest: '' }
  const len = parseInt(match[1], 10)
  const start = (match.index as number) + (match[0] as string).length
  const body = raw.slice(start, start + len)
  const rest = raw.slice(start + len)
  return { body, rest }
}

/**
 * Strip LSP Content-Length framing if present (e.g. "Content-Length: 75\r\n\r\n{...}").
 * Returns the JSON body so the connection reader can parse it.
 * If multiple frames are concatenated, only the first is returned (use splitLspFrames for full split).
 */
function stripLspFraming(raw: string): string {
  const { body } = takeOneLspFrame(raw)
  return body
}

/** Split concatenated LSP frames into separate JSON bodies. */
function splitLspFrames(raw: string): string[] {
  const out: string[] = []
  let rest = raw
  while (rest.length > 0) {
    const { body, rest: next } = takeOneLspFrame(rest)
    if (body.length > 0) out.push(body)
    if (next.length === 0) break
    rest = next
  }
  return out
}

/**
 * Process one JSON-RPC body (after stripping LSP framing): route and optionally push to connection.
 */
function processOneLspBody(body: string): void {
  try {
    const parsed = JSON.parse(body) as { method?: string; id?: string | number; params?: unknown }
    if (parsed && typeof parsed.method === 'string' && parsed.id === undefined) {
      pushE2ELspLogIn(parsed.method, parsed.params)
    }
  } catch {
    // not JSON or not a notification
  }
  routeMessage(body)
  try {
    const parsed = JSON.parse(body) as { id?: string | number; result?: unknown; error?: unknown }
    if (parsed && typeof parsed.id !== 'undefined') {
      const id = parsed.id
      if (deliveredResponseIds.has(id)) {
        return
      }
      deliveredResponseIds.add(id)
    }
    incomingLspPush?.(body)
  } catch (e) {
    console.error('[LSP] Incoming push error (e.g. duplicate response):', e)
  }
}

/**
 * Process one raw message as if received from the worker: run processIncomingWorkerMessage,
 * then split by LSP frames and process each body (routeMessage + incomingLspPush). Used by the worker onmessage and by tests.
 */
export function processIncomingMessage(raw: string): void {
  if (processIncomingWorkerMessage(raw)) return
  const bodies = splitLspFrames(raw)
  if (bodies.length === 0) {
    const body = stripLspFraming(raw)
    if (body.length > 0) processOneLspBody(body)
    return
  }
  for (const body of bodies) {
    processOneLspBody(body)
  }
}

export function initMessageRouter(workerUrl: string | URL, wasmUrl?: string): void {
  if (worker) return
  const url = typeof workerUrl === 'string' ? workerUrl : workerUrl.href
  worker = new Worker(url, { type: 'module' })
  worker.onmessage = (event: MessageEvent<string>) => {
    if (typeof event.data !== 'string') return
    pushE2EWorkerMessage(event.data)
    processIncomingMessage(event.data)
  }
  worker.onerror = (e: ErrorEvent) => {
    const detail = {
      message: e.message,
      filename: e.filename,
      lineno: e.lineno,
      colno: e.colno,
      type: e.type,
      errorString: e.error != null ? String(e.error) : undefined,
    }
    console.error('[LSP Worker]', detail)
    if (typeof window !== 'undefined') {
      const w = window as unknown as { __E2E_LSP_WORKER_ERROR_EVENT__?: unknown; __E2E_WORKER_ERROR_LAST__?: string }
      w.__E2E_LSP_WORKER_ERROR_EVENT__ = detail
      w.__E2E_WORKER_ERROR_LAST__ = JSON.stringify(detail)
    }
  }
  if (wasmUrl) {
    sendToWorker(JSON.stringify({ type: WORKER_MSG_INIT, wasmUrl }))
  } else {
    workerReady = true
    if (readyResolve) {
      readyResolve()
      readyResolve = null
    }
  }
}

function pushE2EWorkerMessage(raw: string): void {
  if (typeof window === 'undefined') return
  const arr = (window as unknown as { __E2E_WORKER_MESSAGES__?: string[] }).__E2E_WORKER_MESSAGES__
  if (!Array.isArray(arr)) return
  arr.push(raw)
}

function pushE2ELspLogOut(method: string): void {
  if (typeof window === 'undefined') return
  const log = (window as unknown as { __E2E_LSP_LOG__?: Array<{ dir: string; method: string; params?: unknown }> })
    .__E2E_LSP_LOG__
  if (!Array.isArray(log)) return
  log.push({ dir: 'out', method })
}

function pushE2ELspLogIn(method: string, params?: unknown): void {
  if (typeof window === 'undefined') return
  const log = (window as unknown as { __E2E_LSP_LOG__?: Array<{ dir: string; method: string; params?: unknown }> })
    .__E2E_LSP_LOG__
  if (!Array.isArray(log)) return
  log.push({ dir: 'in', method, params })
}

export function sendToWorker(message: string): void {
  if (!worker) {
    console.warn('[LSP] Worker not initialized')
    return
  }
  try {
    const body = stripLspFraming(message)
    const parsed = JSON.parse(body) as { method?: string; type?: string }
    if (parsed && typeof parsed.method === 'string') {
      pushE2ELspLogOut(parsed.method)
    }
  } catch {
    // not JSON or control message (e.g. init has type, no method)
  }
  worker.postMessage(message)
}

export function sendRequest(method: string, params?: unknown, id?: string | number): void {
  const msg = {
    jsonrpc: '2.0' as const,
    id: id ?? Math.random().toString(36).slice(2),
    method,
    params,
  }
  sendToWorker(JSON.stringify(msg))
}

let nextStreamRequestId = 0

/** Request a new stream index from the LSP worker (for file-block external streams). Resolves when worker responds. */
export async function requestCreateStreamInput(): Promise<number> {
  await waitForWorkerReady()
  return new Promise((resolve, reject) => {
    const id = nextStreamRequestId++
    const timeoutId = setTimeout(() => {
      const entry = pendingStreamResolvers.get(id)
      if (entry) {
        pendingStreamResolvers.delete(id)
        clearTimeout(entry.timeoutId)
        entry.reject(new Error('createStreamInput response timeout'))
      }
    }, CREATE_STREAM_INPUT_TIMEOUT_MS)
    const entry: PendingStreamResolver = { resolve, reject, timeoutId }
    pendingStreamResolvers.set(id, entry)
    const w = getWorker()
    if (!w) {
      pendingStreamResolvers.delete(id)
      clearTimeout(timeoutId)
      reject(new Error('Worker not initialized'))
      return
    }
    w.postMessage(JSON.stringify({ type: 'createStreamInput', id }))
  })
}

/** Push a chunk (array of numbers) to a stream by index. */
export function sendStreamChunk(index: number, chunk: number[]): void {
  const w = getWorker()
  if (!w) return
  w.postMessage(JSON.stringify({ type: 'pushChunk', index, chunk }))
}

/** Close a stream by index (signal EOF). */
export function closeStream(index: number): void {
  const w = getWorker()
  if (!w) return
  w.postMessage(JSON.stringify({ type: 'closeStream', index }))
}

export function sendNotification(method: string, params?: unknown): void {
  const msg = {
    jsonrpc: '2.0' as const,
    method,
    params,
  }
  sendToWorker(JSON.stringify(msg))
}
