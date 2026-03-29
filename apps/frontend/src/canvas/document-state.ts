import type { CanvasEdge, CanvasNode } from '../lsp/graph-patch'

export type CanvasDocumentState = {
  nodes: CanvasNode[]
  edges: CanvasEdge[]
}

export function addCanvasNode(state: CanvasDocumentState, node: CanvasNode): CanvasDocumentState {
  if (state.nodes.some((current) => current.uri === node.uri)) {
    return state
  }
  return { ...state, nodes: [...state.nodes, node] }
}

export function removeCanvasNode(state: CanvasDocumentState, uri: string): CanvasDocumentState {
  return {
    nodes: state.nodes.filter((node) => node.uri !== uri),
    edges: state.edges.filter((edge) => edge.sourceUri !== uri && edge.targetUri !== uri),
  }
}

export function upsertCanvasEdge(state: CanvasDocumentState, edge: CanvasEdge): CanvasDocumentState {
  const nextEdges = state.edges.filter(
    (current) =>
      !(
        current.targetUri === edge.targetUri &&
        current.targetParamId === edge.targetParamId
      ),
  )
  nextEdges.push(edge)
  return { ...state, edges: nextEdges }
}

export function removeCanvasEdge(
  state: CanvasDocumentState,
  targetUri: string,
  targetParamId: string,
): CanvasDocumentState {
  return {
    ...state,
    edges: state.edges.filter(
      (edge) => !(edge.targetUri === targetUri && edge.targetParamId === targetParamId),
    ),
  }
}

