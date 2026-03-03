/**
 * Pure helpers for project loading: UUID validation and snapshot → graph nodes/edges.
 * Used by useProjectLoader; tested in isolation.
 */

import { nodeIdToUri } from '~/editor/virtual-uri'
import {
  type ComputationOutputHandleId,
  COMPUTATION_OUTPUT_HANDLES,
  COMPUTATION_OUTPUT_HANDLE_RIGHT,
} from '~/lib/constants'
import type { GraphEdge, GraphNode } from '~/store'
import type { ProjectEdge, ProjectSnapshot } from '~/types/project'

function normalizeSourceHandle(s: string | undefined): ComputationOutputHandleId {
  return (COMPUTATION_OUTPUT_HANDLES as readonly string[]).includes(s ?? '')
    ? (s as ComputationOutputHandleId)
    : COMPUTATION_OUTPUT_HANDLE_RIGHT
}

const UUID_REGEX = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i

export function isValidUuid(s: string): boolean {
  return UUID_REGEX.test(s)
}

export function snapshotToGraphNodes(snapshot: ProjectSnapshot): GraphNode[] {
  return snapshot.nodes.map((n) => ({
    id: n.id,
    position: n.position,
    type: n.type,
    uri: nodeIdToUri(n.id),
    initialContent: n.type === 'computation' ? (n.content ?? '') : undefined,
    inputs: n.type === 'computation' && n.inputs?.length ? n.inputs : undefined,
  }))
}

/**
 * Converts snapshot edges to graph edges. Uses targetInputIndex when present.
 * For legacy edges with only targetInputName, resolves to index from target node's inputs (fallback 0).
 */
export function snapshotEdgesToGraphEdges(
  snapshotEdges: ProjectEdge[],
  nodes: GraphNode[],
): GraphEdge[] {
  return snapshotEdges.map((e) => {
    const sourceHandle = normalizeSourceHandle(
      typeof e.sourceHandle === 'string' ? e.sourceHandle : undefined,
    )
    if (typeof e.targetInputIndex === 'number') {
      return {
        sourceId: e.sourceId,
        targetId: e.targetId,
        targetInputIndex: e.targetInputIndex,
        sourceHandle,
      }
    }
    const targetNode = nodes.find((n) => n.id === e.targetId)
    const name = e.targetInputName
    const index =
      name != null && targetNode?.inputs
        ? targetNode.inputs.findIndex((i) => i.name === name)
        : -1
    const targetInputIndex = index >= 0 ? index : 0
    return { sourceId: e.sourceId, targetId: e.targetId, targetInputIndex, sourceHandle }
  })
}
