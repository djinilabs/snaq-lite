/**
 * Singleton message router: holds Web Worker reference, sends JSON-RPC to worker,
 * routes worker messages (LSP responses and custom notifications) to store and client.
 */

import { WORKER_MSG_READY, WORKER_MSG_ERROR, WORKER_MSG_INIT } from '~/lib/constants'
import { routeMessage } from './route-message'

let worker: Worker | null = null
let workerReady = false
let readyResolve: (() => void) | null = null
const readyPromise = new Promise<void>((resolve) => {
  readyResolve = resolve
})

/** Callback to push raw LSP JSON-RPC messages to the language client reader (e.g. for createMessageConnection). */
let incomingLspPush: ((raw: string) => void) | null = null

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

/** Reset workerReady for test isolation. Do not use in production. */
export function resetMessageRouterForTest(): void {
  workerReady = false
}

/**
 * Process an incoming worker message. If it is a control message (ready or error),
 * updates workerReady and returns true (caller should not pass to routeMessage).
 * Otherwise returns false and the caller should pass the raw string to routeMessage.
 */
export function processIncomingWorkerMessage(data: string): boolean {
  try {
    const parsed = JSON.parse(data) as { type?: string; error?: string }
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
        console.error('[LSP Worker]', parsed.error ?? 'Unknown error')
        return true
      }
    }
  } catch {
    // not JSON or not a control message
  }
  return false
}

/**
 * Process one raw message as if received from the worker: run processIncomingWorkerMessage,
 * then routeMessage and incomingLspPush for LSP messages. Used by the worker onmessage and by tests.
 */
export function processIncomingMessage(raw: string): void {
  if (processIncomingWorkerMessage(raw)) return
  routeMessage(raw)
  incomingLspPush?.(raw)
}

export function initMessageRouter(workerUrl: URL, wasmUrl?: string): void {
  if (worker) return
  worker = new Worker(workerUrl, { type: 'module' })
  worker.onmessage = (event: MessageEvent<string>) => {
    if (typeof event.data !== 'string') return
    processIncomingMessage(event.data)
  }
  worker.onerror = (e) => {
    console.error('[LSP Worker]', e)
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

export function sendToWorker(message: string): void {
  if (!worker) {
    console.warn('[LSP] Worker not initialized')
    return
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

export function sendNotification(method: string, params?: unknown): void {
  const msg = {
    jsonrpc: '2.0' as const,
    method,
    params,
  }
  sendToWorker(JSON.stringify(msg))
}
