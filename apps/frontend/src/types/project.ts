/**
 * Project snapshot format for persistence and export/import.
 * URIs are derived when loading via nodeIdToUri; not persisted.
 */

export type ProjectNodeType = 'computation' | 'presentation'

export interface ProjectNode {
  id: string
  position: { x: number; y: number }
  type: ProjectNodeType
  /** Block text; only for computation nodes. */
  content?: string
}

export interface ProjectEdge {
  sourceId: string
  targetId: string
  targetInputName: string
}

export interface ProjectSnapshot {
  id: string
  version?: number
  nodes: ProjectNode[]
  edges: ProjectEdge[]
}

/** Validates shape; returns null if invalid. */
export function parseProjectSnapshot(data: unknown): ProjectSnapshot | null {
  if (data == null || typeof data !== 'object') return null
  const o = data as Record<string, unknown>
  const id = o.id
  const nodes = o.nodes
  const edges = o.edges
  if (typeof id !== 'string' || !Array.isArray(nodes) || !Array.isArray(edges)) return null
  const parsedNodes: ProjectNode[] = []
  for (const n of nodes) {
    if (n == null || typeof n !== 'object') return null
    const no = n as Record<string, unknown>
    if (
      typeof no.id !== 'string' ||
      typeof no.type !== 'string' ||
      (no.type !== 'computation' && no.type !== 'presentation')
    )
      return null
    const pos = no.position
    if (pos == null || typeof pos !== 'object' || typeof (pos as { x?: unknown }).x !== 'number' || typeof (pos as { y?: unknown }).y !== 'number')
      return null
    parsedNodes.push({
      id: no.id,
      position: { x: (pos as { x: number }).x, y: (pos as { y: number }).y },
      type: no.type as ProjectNodeType,
      content: typeof no.content === 'string' ? no.content : undefined,
    })
  }
  const parsedEdges: ProjectEdge[] = []
  for (const e of edges) {
    if (e == null || typeof e !== 'object') return null
    const eo = e as Record<string, unknown>
    if (
      typeof eo.sourceId !== 'string' ||
      typeof eo.targetId !== 'string' ||
      typeof eo.targetInputName !== 'string'
    )
      return null
    parsedEdges.push({
      sourceId: eo.sourceId,
      targetId: eo.targetId,
      targetInputName: eo.targetInputName,
    })
  }
  return {
    id,
    version: typeof o.version === 'number' ? o.version : undefined,
    nodes: parsedNodes,
    edges: parsedEdges,
  }
}
