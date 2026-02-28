/**
 * Pure helper: map deleted React Flow edges + current nodes to (targetUri, targetInputName) for disconnectEdge.
 * Used by GraphCanvas onEdgesDelete; tested in edge-delete-params.test.ts.
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
  targetInputName: string
}

/**
 * Returns params for disconnectEdge for each deleted edge that has a matching node and a string targetHandle.
 */
export function getDisconnectParamsForDeletedEdges(
  deleted: DeletedEdgeLike[],
  nodes: NodeLike[],
): DisconnectParams[] {
  const result: DisconnectParams[] = []
  for (const edge of deleted) {
    const targetUri = nodes.find((n) => n.id === edge.target)?.uri
    const targetInputName =
      typeof edge.targetHandle === 'string' ? edge.targetHandle : undefined
    if (targetUri && targetInputName) {
      result.push({ targetUri, targetInputName })
    }
  }
  return result
}
