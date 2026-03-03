/**
 * Edge-delete helpers: map deleted React Flow edges + nodes to disconnect params, and apply disconnect for each.
 * targetHandle is the input index string (e.g. "0", "1"). Used by GraphCanvas onEdgesDelete.
 */

export interface DeletedEdgeLike {
  target: string
  targetHandle?: string | null
}

export interface NodeLike {
  id: string
  uri: string
}

export interface DisconnectParams {
  targetUri: string
  targetInputIndex: number
}

/**
 * Returns params for disconnectEdge for each deleted edge that has a matching node and a valid numeric targetHandle (input index).
 */
export function getDisconnectParamsForDeletedEdges(
  deleted: DeletedEdgeLike[],
  nodes: NodeLike[],
): DisconnectParams[] {
  const result: DisconnectParams[] = []
  for (const edge of deleted) {
    const targetUri = nodes.find((n) => n.id === edge.target)?.uri
    const raw =
      typeof edge.targetHandle === 'string' ? edge.targetHandle : undefined
    const targetInputIndex = raw != null ? Number(raw) : NaN
    if (targetUri != null && Number.isInteger(targetInputIndex) && targetInputIndex >= 0) {
      result.push({ targetUri, targetInputIndex })
    }
  }
  return result
}

/**
 * Resolves disconnect params from deleted edges and nodes, then invokes disconnect for each (synchronously).
 * Used by GraphCanvas onEdgesDelete; exported for unit tests.
 */
export function applyDisconnectForDeletedEdges(
  deleted: DeletedEdgeLike[],
  nodes: NodeLike[],
  disconnect: (targetUri: string, targetInputIndex: number) => void,
): void {
  const params = getDisconnectParamsForDeletedEdges(deleted, nodes)
  for (const { targetUri, targetInputIndex } of params) {
    disconnect(targetUri, targetInputIndex)
  }
}
