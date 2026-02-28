/**
 * Dispatches incoming LSP messages: responses → request-id callbacks or Monaco;
 * custom notifications (nodeSignatureUpdated, widgetDataUpdate) → store or widget handlers.
 */

import type {
  JsonRpcMessage,
  JsonRpcResponse,
  JsonRpcNotification,
  NodeSignatureUpdatedParams,
  WidgetDataUpdateParams,
} from './types'
import { isResponse, isNotification } from './types'

export type OnNodeSignatureUpdated = (params: NodeSignatureUpdatedParams) => void
export type OnWidgetDataUpdate = (params: WidgetDataUpdateParams) => void
export type OnLspResponse = (response: JsonRpcResponse) => void

export interface MessageRouterHandlers {
  onNodeSignatureUpdated?: OnNodeSignatureUpdated
  onWidgetDataUpdate?: OnWidgetDataUpdate
  /** Called for every LSP response (id + result/error); used by client to resolve promises. */
  onLspResponse?: OnLspResponse
}

let handlers: MessageRouterHandlers = {}

export function setMessageRouterHandlers(h: MessageRouterHandlers): void {
  handlers = { ...handlers, ...h }
}

/** Reset handlers (e.g. for test isolation). */
export function clearMessageRouterHandlers(): void {
  handlers = {}
}

export function routeMessage(raw: string): void {
  let msg: JsonRpcMessage
  try {
    msg = JSON.parse(raw) as JsonRpcMessage
  } catch {
    return
  }

  if (isResponse(msg)) {
    handlers.onLspResponse?.(msg)
    return
  }

  if (isNotification(msg)) {
    const notification = msg as JsonRpcNotification
    switch (notification.method) {
      case 'snaqlite/graph/nodeSignatureUpdated':
        handlers.onNodeSignatureUpdated?.(notification.params as NodeSignatureUpdatedParams)
        break
      case 'snaqlite/graph/widgetDataUpdate':
        handlers.onWidgetDataUpdate?.(notification.params as WidgetDataUpdateParams)
        break
      default:
        // Other LSP notifications (e.g. textDocument/publishDiagnostics) can be handled here
        break
    }
  }
}
