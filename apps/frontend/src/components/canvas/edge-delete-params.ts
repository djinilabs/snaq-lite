/**
 * Pure helper: map deleted React Flow edges + current nodes to (targetUri, targetInputIndex) for disconnectEdge.
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
