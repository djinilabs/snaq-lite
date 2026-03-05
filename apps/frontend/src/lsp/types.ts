/**
 * JSON-RPC and LSP types for snaq-lite LSP and custom graph/widget methods.
 * Aligned with crates/snaq-lite-lsp pubsub.rs and LSP spec.
 */

// ---- JSON-RPC ----

export interface JsonRpcRequest {
  jsonrpc: '2.0'
  id: string | number
  method: string
  params?: unknown
}

export interface JsonRpcResponse {
  jsonrpc: '2.0'
  id: string | number
  result?: unknown
  error?: { code: number; message: string; data?: unknown }
}

export interface JsonRpcNotification {
  jsonrpc: '2.0'
  method: string
  params?: unknown
}

export type JsonRpcMessage = JsonRpcRequest | JsonRpcResponse | JsonRpcNotification

export function isRequest(msg: JsonRpcMessage): msg is JsonRpcRequest {
  return 'id' in msg && 'method' in msg && !('result' in msg) && !('error' in msg)
}

export function isResponse(msg: JsonRpcMessage): msg is JsonRpcResponse {
  return 'id' in msg && (('result' in msg) || ('error' in msg))
}

export function isNotification(msg: JsonRpcMessage): msg is JsonRpcNotification {
  return !('id' in msg) && 'method' in msg
}

// ---- Custom notifications (server → client) ----

export interface NodeInputPort {
  name: string
  type: string
}

export interface NodeSignatureUpdatedParams {
  uri: string
  inputs: NodeInputPort[]
  outputType?: string | null
}

export type WidgetDataStatus = 'Running' | 'Completed' | 'Cancelled' | 'Error'

export type ResultType = 'Scalar' | 'Vector' | 'Map' | 'Undefined'

export interface ResultSummary {
  length?: number
  keys?: string[]
  keyCount?: number
}

export interface WidgetDataUpdateParams {
  widgetId: string
  status: WidgetDataStatus
  payload?: {
    elements?: Array<{ display: string } | null | { kind: 'error'; message: string }>
    offset?: number
    count?: number
    display?: string
    totalElements?: number
    resultType?: ResultType
    resultSummary?: ResultSummary
    message?: string
    reason?: string
  }
}

// ---- Custom request params ----

export interface GraphConnectParams {
  sourceUri: string
  targetUri: string
  targetInputName: string
}

export interface GraphDisconnectParams {
  targetUri: string
  targetInputName: string
}

export interface SubscribeWidgetParams {
  widgetId: string
  sourceUri: string
}

export interface UnsubscribeWidgetParams {
  widgetId: string
}

// ---- fetchResultSlice ----

export type PathSegment = number | string

export interface FetchResultSliceParams {
  widgetId: string
  path: PathSegment[]
  offset: number
  limit: number
}

export interface FetchResultSliceResponse {
  elements: ResultSliceElement[]
  totalCount: number
  hasMore: boolean
}

export type ResultSliceElement =
  | { display: string }
  | { type: 'vector'; path: PathSegment[]; length?: number }
  | { type: 'map'; path: PathSegment[]; keys?: string[]; keyCount?: number }
  | { key: string; value: ResultSliceElement }
  | null
