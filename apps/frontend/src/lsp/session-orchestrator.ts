import type { LspClient } from './client'
import type { BootstrapSessionResponse } from './types'

export type CanvasNodeDocument = {
  uri: string
  source: string
  version?: number
}

export type CanvasEdgeDocument = {
  sourceUri: string
  targetUri: string
  targetParamId: string
}

export type CanvasDocument = {
  canvasId?: string
  revision?: number
  layout?: Record<string, unknown>
  nodes: CanvasNodeDocument[]
  edges: CanvasEdgeDocument[]
}

export async function ensureCanvasSession(
  client: LspClient,
  canvasId: string,
  snapshot?: CanvasDocument,
): Promise<BootstrapSessionResponse> {
  const bootstrap = await client.bootstrapSession()
  if (!bootstrap.canvasId || bootstrap.canvasId === canvasId) {
    if (snapshot) {
      await client.sendRequest('snaqlite/graph/importCanvasDocument', { canvasDocument: snapshot })
    }
    return bootstrap
  }

  if (!bootstrap.runtimeDrained) {
    await client.sendRequest('snaqlite/graph/resetNamespace', {
      uriPrefix: `snaq://${bootstrap.canvasId}/`,
    })
  }

  if (snapshot) {
    await client.sendRequest('snaqlite/graph/importCanvasDocument', { canvasDocument: snapshot })
  }

  return client.bootstrapSession()
}
