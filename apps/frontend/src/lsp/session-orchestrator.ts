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

/** One JSON-RPC request after the initial `bootstrapSession` (method + params only). */
export type PlannedLspRequest = {
  method: string
  params: unknown
}

/**
 * Plan the `bootstrapSession` / `resetNamespace` / `importCanvasDocument` sequence for a canvas snapshot.
 * The first step is always `snaqlite/bootstrapSession` (already executed by `ensureCanvasSession` before planning).
 */
export function planEnsureCanvasSessionRequests(
  canvasId: string,
  snapshot: CanvasDocument | undefined,
  bootstrap: { canvasId?: string; runtimeDrained: boolean },
): PlannedLspRequest[] {
  const out: PlannedLspRequest[] = [{ method: 'snaqlite/bootstrapSession', params: {} }]
  const active = bootstrap.canvasId
  const sameOrEmpty = !active || active === canvasId
  if (sameOrEmpty) {
    if (snapshot) {
      out.push({
        method: 'snaqlite/graph/importCanvasDocument',
        params: { canvasDocument: snapshot },
      })
    }
    return out
  }
  if (!bootstrap.runtimeDrained) {
    out.push({
      method: 'snaqlite/graph/resetNamespace',
      params: { uriPrefix: `snaq://${active}/` },
    })
  }
  if (snapshot) {
    out.push({
      method: 'snaqlite/graph/importCanvasDocument',
      params: { canvasDocument: snapshot },
    })
  }
  out.push({ method: 'snaqlite/bootstrapSession', params: {} })
  return out
}

export async function ensureCanvasSession(
  client: LspClient,
  canvasId: string,
  snapshot?: CanvasDocument,
): Promise<BootstrapSessionResponse> {
  const bootstrap = await client.bootstrapSession()
  const plan = planEnsureCanvasSessionRequests(canvasId, snapshot, bootstrap)
  let latest = bootstrap
  for (const step of plan.slice(1)) {
    if (step.method === 'snaqlite/bootstrapSession') {
      latest = await client.bootstrapSession()
    } else {
      await client.sendRequest(step.method, step.params)
    }
  }
  return latest
}
