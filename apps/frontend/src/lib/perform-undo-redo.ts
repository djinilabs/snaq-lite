/**
 * Shared undo/redo actions: restore graph state then sync Monaco models and LSP graph.
 * Used by the canvas route (keyboard) and toolbar so that undo/redo also re-establishes
 * LSP edges (fixes "input has no effect" after undo of edge removal).
 */

import { syncModelsToGraphNodes } from '~/lib/project-storage'
import { syncLoadedGraphToLsp } from '~/lib/sync-graph-to-lsp'
import { useGraphStore } from '~/store'

/**
 * Pops the undo stack, restores nodes and edges, syncs Monaco models to restored content,
 * then syncs the graph to the LSP (didOpen + graph/connect) so restored edges take effect.
 * No-op if undo stack is empty. LSP sync errors are swallowed so the UI stays consistent.
 */
export function performUndo(): void {
  useGraphStore.getState().undo()
  const { nodes, edges } = useGraphStore.getState()
  syncModelsToGraphNodes(nodes)
  void syncLoadedGraphToLsp(nodes, edges).catch(() => {})
}

/**
 * Pops the redo stack, restores nodes and edges, syncs Monaco models to restored content,
 * then syncs the graph to the LSP so restored edges take effect.
 * No-op if redo stack is empty. LSP sync errors are swallowed so the UI stays consistent.
 */
export function performRedo(): void {
  useGraphStore.getState().redo()
  const { nodes, edges } = useGraphStore.getState()
  syncModelsToGraphNodes(nodes)
  void syncLoadedGraphToLsp(nodes, edges).catch(() => {})
}
