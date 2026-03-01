/**
 * Pure helpers for building React Flow node data from graph store state.
 * Used by graph-canvas; tested without importing Monaco or React Flow.
 */

import type { GraphNode, GraphEdge } from '~/store'

export interface FlowNodeData {
  uri: string
  label: string
  sourceUri: string
}

/**
 * Computes flow node data. For presentation nodes, sourceUri is the source node's URI
 * when an edge targets this node; otherwise ''. If multiple edges target the same node,
 * the first edge's source is used.
 */
export function getFlowNodeData(
  n: GraphNode,
  storeNodes: GraphNode[],
  storeEdges: GraphEdge[],
): FlowNodeData {
  const sourceUri =
    n.type === 'presentation'
      ? (() => {
          const edge = storeEdges.find((e) => e.targetId === n.id)
          if (!edge) return ''
          const sourceNode = storeNodes.find((s) => s.id === edge.sourceId)
          return sourceNode?.uri ?? ''
        })()
      : n.uri
  return {
    uri: n.uri,
    label: n.type === 'computation' ? 'Computation' : 'Presentation',
    sourceUri,
  }
}
