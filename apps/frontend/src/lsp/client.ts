import { LspWorkerConnection, type NotificationHandler } from './worker-connection'
import type {
  ApplyGraphPatchResponse,
  BootstrapSessionResponse,
  FetchResultSliceResponse,
  GraphPatchOperation,
  JsonRpcNotification,
} from './types'

export type LspClient = {
  initialize: () => Promise<void>
  onNotification: (handler: NotificationHandler) => void
  sendRequest: <TResult = unknown>(method: string, params?: unknown) => Promise<TResult>
  sendNotification: (method: string, params?: unknown) => Promise<void>
  bootstrapSession: () => Promise<BootstrapSessionResponse>
  applyPatch: (operations: GraphPatchOperation[]) => Promise<ApplyGraphPatchResponse>
  fetchResultSlice: (params: {
    resultHandle: string
    path: Array<number | string>
    offset: number
    limit: number
    cursor?: string
  }) => Promise<FetchResultSliceResponse>
  close: () => void
}

export function createLspClient({
  workerUrl,
  wasmUrl,
  workerFactory,
}: {
  workerUrl?: string
  wasmUrl: string
  workerFactory?: () => Worker
}): LspClient {
  if (!workerFactory && !workerUrl) {
    throw new Error('createLspClient requires workerUrl when workerFactory is not provided')
  }
  const connection = new LspWorkerConnection(
    workerFactory ?? (() => new Worker(workerUrl as string, { type: 'module' })),
    wasmUrl,
  )
  return {
    initialize: async () => {
      await connection.request('initialize', {
        processId: null,
        rootUri: null,
        capabilities: {},
      })
      await connection.notify('initialized', {})
    },
    onNotification: (handler: (notification: JsonRpcNotification) => void) => {
      connection.onNotification(handler)
    },
    sendRequest: async <TResult>(method: string, params?: unknown) =>
      connection.request<TResult>(method, params),
    sendNotification: async (method: string, params?: unknown) =>
      connection.notify(method, params),
    bootstrapSession: async () =>
      connection.request<BootstrapSessionResponse>('snaqlite/bootstrapSession', {}),
    applyPatch: async (operations: GraphPatchOperation[]) =>
      connection.request<ApplyGraphPatchResponse>('snaqlite/graph/applyPatch', { operations }),
    fetchResultSlice: async (params) =>
      connection.request<FetchResultSliceResponse>('snaqlite/graph/fetchResultSlice', params),
    close: () => connection.close(),
  }
}
