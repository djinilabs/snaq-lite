/**
 * Logic to send snaqlite/graph/connect and disconnect via LSP client and update graph store.
 */

import { waitForLanguageClient } from '~/lsp/language-client-singleton'
import { LSP_METHOD_GRAPH_CONNECT, LSP_METHOD_GRAPH_DISCONNECT } from '~/lib/constants'
import { useGraphStore } from '~/store'
import { useUIStore } from '~/store'

function errorMessage(e: unknown): string {
  return e instanceof Error ? e.message : String(e)
}

const LSP_WAIT_MS = 15_000

/**
 * Optimistic connect: add edge to store and draw wire immediately, then send LSP connect.
 * If the LSP is not ready yet, waits up to LSP_WAIT_MS for it before connecting.
 * On LSP error, drop the pending wire from the store and show error toast.
 */
export async function connectEdge(
  sourceUri: string,
  targetUri: string,
  targetInputName: string,
): Promise<boolean> {
  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) {
    useUIStore.getState().addToast('Editor is still loading. Please try again in a moment.', 'error')
    return false
  }
  const sourceId = useGraphStore.getState().nodes.find((n) => n.uri === sourceUri)?.id
  const targetId = useGraphStore.getState().nodes.find((n) => n.uri === targetUri)?.id
  if (!sourceId || !targetId) return false

  useGraphStore.getState().addEdge({ sourceId, targetId, targetInputName })
  try {
    await langClient.sendRequest(LSP_METHOD_GRAPH_CONNECT, {
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
 * If the LSP is not ready yet, waits up to LSP_WAIT_MS for it.
 * On LSP error, re-add the edge (rollback) and show error toast.
 */
export async function disconnectEdge(
  targetUri: string,
  targetInputName: string,
): Promise<void> {
  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) {
    useUIStore.getState().addToast('Editor is still loading. Please try again in a moment.', 'error')
    return
  }
  const state = useGraphStore.getState()
  const targetId = state.nodes.find((n) => n.uri === targetUri)?.id
  if (!targetId) return

  const edge = state.edges.find(
    (e) => e.targetId === targetId && e.targetInputName === targetInputName,
  )
  const sourceId = edge?.sourceId

  state.removeEdge(targetId, targetInputName)
  try {
    await langClient.sendRequest(LSP_METHOD_GRAPH_DISCONNECT, {
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
