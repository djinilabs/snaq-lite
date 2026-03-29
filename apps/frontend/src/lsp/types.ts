export type JsonRpcId = number

export interface JsonRpcRequest<TParams = unknown> {
  jsonrpc: '2.0'
  id: JsonRpcId
  method: string
  params?: TParams
}

export interface JsonRpcNotification<TParams = unknown> {
  jsonrpc: '2.0'
  method: string
  params?: TParams
}

export interface JsonRpcSuccess<TResult = unknown> {
  jsonrpc: '2.0'
  id: JsonRpcId
  result: TResult
}

export interface JsonRpcFailure {
  jsonrpc: '2.0'
  id: JsonRpcId
  error: {
    code: number
    message: string
    data?: unknown
  }
}

export type JsonRpcInbound = JsonRpcSuccess | JsonRpcFailure | JsonRpcNotification

export interface BootstrapSessionResponse {
  canvasId?: string
  canvasRevision: number
  openDocuments: number
  subscriptions: number
  widgets: number
  resultHandles: number
  runtimeDrained: boolean
}

export interface ApplyGraphPatchResponse {
  appliedOperations: number
  affectedUris: string[]
}

export interface FetchResultSliceResponse {
  elements: Array<unknown>
  totalCount: number
  hasMore: boolean
  nextCursor?: string
}

export interface SubscribeNodeResponse {
  subscriptionId: string
  resultHandle?: string
}

export type PublishStatus = 'Running' | 'Completed' | 'Error' | 'Cancelled'

export interface PublishNodeResultParams {
  subscriptionId: string
  status: PublishStatus
  revision?: number
  canvasId?: string
  uri?: string
  data?: Record<string, unknown>
}

export interface NodeSignatureInput {
  name: string
  paramId: string
  type: string
}

export interface NodeSignatureUpdatedParams {
  uri: string
  inputs: NodeSignatureInput[]
  outputType?: string | null
}

export interface WidgetDataUpdateParams {
  widgetId: string
  status: PublishStatus
  revision?: number
  canvasId?: string
  uri?: string
  payload?: Record<string, unknown>
}

export type GraphPatchOperation =
  | { op: 'addNode'; uri: string; source: string; version?: number }
  | { op: 'removeNode'; uri: string }
  | { op: 'setNodeSource'; uri: string; source: string }
  | {
      op: 'connect'
      sourceUri: string
      targetUri: string
      targetInputName: string
    }
  | { op: 'disconnect'; targetUri: string; targetInputName: string }
  | { op: 'renameParam'; uri: string; paramId: string; newName: string }
  | {
      op: 'addParam'
      uri: string
      paramId: string
      name: string
      typeName: string
    }
  | { op: 'removeParam'; uri: string; paramId: string }

export interface WorkerInitMessage {
  type: 'init'
  wasmUrl: string
}

export interface WorkerReadyMessage {
  type: 'snaqlite-worker-ready'
}

export interface WorkerErrorMessage {
  type: 'snaqlite-worker-error'
  error: string
}

export type WorkerControlMessage = WorkerInitMessage | WorkerReadyMessage | WorkerErrorMessage
