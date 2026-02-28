/**
 * Helpers for text model lifecycle: detect which node IDs were removed from the graph
 * so their Monaco models can be disposed.
 */

/**
 * Returns node IDs that were in the previous set but are not in the current nodes list.
 * Used to dispose text models when nodes are removed from the graph.
 */
export function getRemovedNodeIds(
  prevIds: Set<string>,
  nodes: { id: string }[],
): string[] {
  const currentIds = new Set(nodes.map((n) => n.id))
  const removed: string[] = []
  for (const id of prevIds) {
    if (!currentIds.has(id)) removed.push(id)
  }
  return removed
}
