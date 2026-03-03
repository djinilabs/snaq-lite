/**
 * Pure helper to convert graph store edges to React Flow edge shape.
 * Used by graph-canvas; tested without importing React Flow.
 */

import { COMPUTATION_OUTPUT_HANDLE_RIGHT } from '~/lib/constants'
import type { GraphEdge } from '~/store'

export interface FlowEdgeShape {
  id: string
  source: string
  target: string
  sourceHandle: string
  targetHandle: string
}

/**
 * Converts a store GraphEdge to the shape expected by React Flow (id, source, target, sourceHandle, targetHandle).
 * sourceHandle defaults to right-handle when absent for backward compatibility.
 */
export function graphEdgeToFlowEdge(e: GraphEdge): FlowEdgeShape {
  return {
    id: `${e.sourceId}-${e.targetId}-${e.targetInputIndex}`,
    source: e.sourceId,
    target: e.targetId,
    sourceHandle: e.sourceHandle ?? COMPUTATION_OUTPUT_HANDLE_RIGHT,
    targetHandle: String(e.targetInputIndex),
  }
}
