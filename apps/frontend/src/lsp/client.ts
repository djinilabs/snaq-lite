/**
 * Thin LSP client: request(method, params) returns a Promise that resolves when
 * the router receives the matching response; sendNotification for fire-and-forget.
 */

import type { JsonRpcResponse } from './types'
import { setMessageRouterHandlers, routeMessage } from './route-message'
import { sendToWorker, initMessageRouter } from './message-router'

const pending = new Map<string | number, { resolve: (r: unknown) => void; reject: (e: Error) => void }>()

function handleResponse(response: JsonRpcResponse): void {
  const id = response.id
  const p = pending.get(id)
  if (!p) return
  pending.delete(id)
  if (response.error) {
    p.reject(new Error(response.error.message))
  } else {
    p.resolve(response.result)
  }
}

let handlersRegistered = false

function ensureHandlers(): void {
  if (handlersRegistered) return
  setMessageRouterHandlers({ onLspResponse: handleResponse })
  handlersRegistered = true
}

/**
 * Initialize the LSP worker and client. Call once at app startup.
 * Pass the worker script URL, e.g. new URL('./worker/lsp.worker.ts', import.meta.url) from a file in src.
 */
export function initLspClient(workerUrl: URL): void {
  ensureHandlers()
  initMessageRouter(workerUrl)
}

/**
 * Send a JSON-RPC request and return a Promise that resolves with the result.
 */
export function request<T = unknown>(method: string, params?: unknown, id?: string | number): Promise<T> {
  ensureHandlers()
  const reqId = id ?? Math.random().toString(36).slice(2)
  const msg = {
    jsonrpc: '2.0' as const,
    id: reqId,
    method,
    params,
  }
  return new Promise<T>((resolve, reject) => {
    pending.set(reqId, {
      resolve: (r) => resolve(r as T),
      reject,
    })
    sendToWorker(JSON.stringify(msg))
  })
}

/**
 * Send a JSON-RPC notification (no response expected).
 */
export function sendNotification(method: string, params?: unknown): void {
  const msg = {
    jsonrpc: '2.0' as const,
    method,
    params,
  }
  sendToWorker(JSON.stringify(msg))
}

/**
 * Process a raw message (e.g. from tests or alternate transport). Used by router.
 */
export function processRawMessage(raw: string): void {
  routeMessage(raw)
}
