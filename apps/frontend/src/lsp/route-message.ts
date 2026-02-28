/**
 * Dispatches incoming LSP messages: responses → request-id callbacks or Monaco;
 * custom notifications (nodeSignatureUpdated, widgetDataUpdate, publishDiagnostics) → store or registered handler.
 */

import type {
  JsonRpcMessage,
  JsonRpcResponse,
  JsonRpcNotification,
  NodeSignatureUpdatedParams,
  WidgetDataUpdateParams,
} from './types'
import { isResponse, isNotification } from './types'

const LSP_DIAGNOSTICS_METHOD = 'textDocument/publishDiagnostics'

export type OnNodeSignatureUpdated = (params: NodeSignatureUpdatedParams) => void
export type OnWidgetDataUpdate = (params: WidgetDataUpdateParams) => void
export type OnLspResponse = (response: JsonRpcResponse) => void

export interface PublishDiagnosticsParams {
  uri?: string
  diagnostics?: Array<{
    range?: { start?: { line?: number; character?: number }; end?: { line?: number; character?: number } }
    message?: string
    severity?: number
  }>
}

export type OnPublishDiagnostics = (params: PublishDiagnosticsParams) => void

export interface MessageRouterHandlers {
  onNodeSignatureUpdated?: OnNodeSignatureUpdated
  onWidgetDataUpdate?: OnWidgetDataUpdate
  /** Called for every LSP response (id + result/error); used by client to resolve promises. */
  onLspResponse?: OnLspResponse
  /** Called when server sends textDocument/publishDiagnostics; app can apply to Monaco. */
  onPublishDiagnostics?: OnPublishDiagnostics
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
      case LSP_DIAGNOSTICS_METHOD:
        handlers.onPublishDiagnostics?.(notification.params as PublishDiagnosticsParams)
        break
      default:
        break
    }
  }
}
