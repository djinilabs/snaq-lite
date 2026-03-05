/**
 * Pure helpers for building React Flow node data from graph store state.
 * Used by graph-canvas; tested without importing Monaco or React Flow.
 */

import type { GraphNode, GraphEdge } from '~/store'
import { fileBlockLabel } from './file-block-node'

export interface FlowNodeData {
  uri: string
  label: string
  sourceUri: string
  /** For file nodes: blob URL, data URL, or https. */
  url?: string
}

/**
 * Computes flow node data. For presentation nodes, sourceUri is the source node's URI
 * when an edge targets this node; otherwise ''. File nodes are output-only (sourceUri '').
 */
export function getFlowNodeData(
  n: GraphNode,
  storeNodes: GraphNode[],
  storeEdges: GraphEdge[],
): FlowNodeData {
  let sourceUri: string
  let label: string
  if (n.type === 'presentation') {
    const edge = storeEdges.find((e) => e.targetId === n.id)
    sourceUri = edge ? (storeNodes.find((s) => s.id === edge.sourceId)?.uri ?? '') : ''
    label = 'Presentation'
  } else if (n.type === 'file') {
    sourceUri = ''
    label = n.fileName ?? fileBlockLabel(n.url)
    return { uri: n.uri, label, sourceUri: '', ...(n.url ? { url: n.url } : {}) }
  } else {
    sourceUri = n.uri
    label = 'Computation'
  }
  return {
    uri: n.uri,
    label,
    sourceUri,
  }
}
