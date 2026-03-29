import { LspWorkerConnection, type NotificationHandler } from './worker-connection'
import type {
  ApplyGraphPatchResponse,
  BootstrapSessionResponse,
  FetchResultSliceResponse,
  GraphPatchOperation,
  JsonRpcNotification,
  SubscribeNodeResponse,
} from './types'

export type LspClient = {
  initialize: () => Promise<void>
  onNotification: (handler: NotificationHandler) => void
  sendRequest: <TResult = unknown>(method: string, params?: unknown) => Promise<TResult>
  sendNotification: (method: string, params?: unknown) => Promise<void>
  didOpen: (params: { uri: string; text: string; version?: number }) => Promise<void>
  didChange: (params: { uri: string; text: string; version?: number }) => Promise<void>
  didClose: (uri: string) => Promise<void>
  subscribeNode: (sourceUri: string) => Promise<SubscribeNodeResponse>
  unsubscribeNode: (subscriptionId: string) => Promise<void>
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
  const documentVersions = new Map<string, number>()

  function nextVersionForDidOpen(uri: string, version?: number): number {
    const next = version ?? 1
    documentVersions.set(uri, next)
    return next
  }

  function nextVersionForDidChange(uri: string, version?: number): number {
    const current = documentVersions.get(uri)
    const next = version ?? (current ?? 0) + 1
    if (current !== undefined && next <= current) {
      throw new Error(
        `didChange version must be greater than current version (${current}) for ${uri}`,
      )
    }
    documentVersions.set(uri, next)
    return next
  }

  function clearVersionForDidClose(uri: string): void {
    documentVersions.delete(uri)
  }

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
    didOpen: async ({ uri, text, version }) =>
      connection.notify('textDocument/didOpen', {
        textDocument: {
          uri,
          languageId: 'snaq',
          version: nextVersionForDidOpen(uri, version),
          text,
        },
      }),
    didChange: async ({ uri, text, version }) =>
      connection.notify('textDocument/didChange', {
        textDocument: { uri, version: nextVersionForDidChange(uri, version) },
        contentChanges: [{ text }],
      }),
    didClose: async (uri: string) => {
      clearVersionForDidClose(uri)
      return connection.notify('textDocument/didClose', {
        textDocument: { uri },
      })
    },
    subscribeNode: async (sourceUri: string) =>
      connection.request<SubscribeNodeResponse>('snaqlite/subscribeNode', { sourceUri }),
    unsubscribeNode: async (subscriptionId: string) =>
      connection.request('snaqlite/unsubscribeNode', { subscriptionId }),
    bootstrapSession: async () =>
      connection.request<BootstrapSessionResponse>('snaqlite/bootstrapSession', {}),
    applyPatch: async (operations: GraphPatchOperation[]) =>
      connection.request<ApplyGraphPatchResponse>('snaqlite/graph/applyPatch', { operations }),
    fetchResultSlice: async (params) =>
      connection.request<FetchResultSliceResponse>('snaqlite/graph/fetchResultSlice', params),
    close: () => connection.close(),
  }
}
