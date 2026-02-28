/**
 * Logic to send snaqlite/graph/connect and disconnect via LSP client and update graph store.
 */

import { request } from '~/lsp'
import { LSP_METHOD_GRAPH_CONNECT, LSP_METHOD_GRAPH_DISCONNECT } from '~/lib/constants'
import { useGraphStore } from '~/store'
import { useUIStore } from '~/store'

function errorMessage(e: unknown): string {
  return e instanceof Error ? e.message : String(e)
}

/**
 * Optimistic connect: add edge to store and draw wire immediately, then send LSP connect.
 * On LSP error, drop the pending wire from the store and show error toast.
 */
export async function connectEdge(
  sourceUri: string,
  targetUri: string,
  targetInputName: string,
): Promise<boolean> {
  const sourceId = useGraphStore.getState().nodes.find((n) => n.uri === sourceUri)?.id
  const targetId = useGraphStore.getState().nodes.find((n) => n.uri === targetUri)?.id
  if (!sourceId || !targetId) return false

  useGraphStore.getState().addEdge({ sourceId, targetId, targetInputName })
  try {
    await request(LSP_METHOD_GRAPH_CONNECT, {
      sourceUri,
      targetUri,
      targetInputName,
    })
    return true
  } catch (e) {
    useGraphStore.getState().removeEdge(targetId, targetInputName)
    useGraphStore.getState().clearPendingEdge()
    useUIStore.getState().addToast(errorMessage(e), 'error')
    return false
  }
}

/**
 * Optimistic disconnect: remove edge from store, then notify LSP.
 * On LSP error, re-add the edge (rollback) and show error toast.
 */
export async function disconnectEdge(
  targetUri: string,
  targetInputName: string,
): Promise<void> {
  const state = useGraphStore.getState()
  const targetId = state.nodes.find((n) => n.uri === targetUri)?.id
  if (!targetId) return

  const edge = state.edges.find(
    (e) => e.targetId === targetId && e.targetInputName === targetInputName,
  )
  const sourceId = edge?.sourceId

  state.removeEdge(targetId, targetInputName)
  try {
    await request(LSP_METHOD_GRAPH_DISCONNECT, {
      targetUri,
      targetInputName,
    })
  } catch (e) {
    if (sourceId != null) {
      useGraphStore.getState().addEdge({ sourceId, targetId, targetInputName })
    }
    useUIStore.getState().addToast(errorMessage(e), 'error')
  }
}
