/**
 * Logic to send snaqlite/graph/connect and disconnect via LSP client and update graph store.
 */

import { request } from '~/lsp'
import { LSP_METHOD_GRAPH_CONNECT } from '~/lib/constants'
import { useGraphStore } from '~/store'
import { useUIStore } from '~/store'

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
    useUIStore.getState().addToast((e as Error).message, 'error')
    return false
  }
}

export function disconnectEdge(targetUri: string, targetInputName: string): void {
  const targetId = useGraphStore.getState().nodes.find((n) => n.uri === targetUri)?.id
  if (targetId) {
    useGraphStore.getState().removeEdge(targetId, targetInputName)
  }
  // Optionally call LSP disconnect: request(LSP_METHOD_GRAPH_DISCONNECT, { targetUri, targetInputName })
}
