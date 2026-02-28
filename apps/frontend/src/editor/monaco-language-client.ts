/**
 * Single shared language client: forwards LSP requests/responses via the message router.
 * Monaco editors use this transport so one LSP connection serves all computation boxes.
 * Full integration with monaco-languageclient can wire this as MessageTransports.
 */

import { sendToWorker } from '~/lsp/message-router'
import { setMessageRouterHandlers } from '~/lsp/route-message'
import type { JsonRpcResponse } from '~/lsp/types'

/** Callbacks keyed by request id; resolved when router receives the response. */
const pending = new Map<string | number, (response: JsonRpcResponse) => void>()

function handleResponse(response: JsonRpcResponse): void {
  const id = response.id
  const cb = pending.get(id)
  if (cb) {
    pending.delete(id)
    cb(response)
  }
}

let registered = false

export function initMonacoLanguageClientTransport(): void {
  if (registered) return
  setMessageRouterHandlers({ onLspResponse: handleResponse })
  registered = true
}

/**
 * Send a JSON-RPC request and register a one-off callback for the response.
 * Used by adapters that need to match response by id.
 */
export function sendRequest(
  method: string,
  params: unknown,
  id: string | number,
): void {
  const msg = { jsonrpc: '2.0' as const, id, method, params }
  pending.set(id, () => {})
  sendToWorker(JSON.stringify(msg))
}

/**
 * Register a callback for a given request id. Call before sendRequest.
 */
export function registerResponseHandler(
  id: string | number,
  cb: (response: JsonRpcResponse) => void,
): void {
  pending.set(id, cb)
}

export function sendNotification(method: string, params?: unknown): void {
  const msg = { jsonrpc: '2.0' as const, method, params }
  sendToWorker(JSON.stringify(msg))
}
