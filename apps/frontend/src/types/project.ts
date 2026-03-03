/**
 * Project snapshot format for persistence and export/import.
 * URIs are derived when loading via nodeIdToUri; not persisted.
 */

export type ProjectNodeType = 'computation' | 'presentation' | 'file'

/** Input port for a computation block (name used as $name in script). */
export interface ProjectNodeInput {
  name: string
  type: string
}

export interface ProjectNode {
  id: string
  position: { x: number; y: number }
  type: ProjectNodeType
  /** Block text; only for computation nodes. */
  content?: string
  /** Input ports; only for computation nodes. Editable in UI, not in block text. */
  inputs?: ProjectNodeInput[]
  /** URL for file nodes (blob, data, or https). Optional; used when type === 'file'. */
  url?: string
}

export interface ProjectEdge {
  sourceId: string
  targetId: string
  /** Index of the target node's input port (0-based). Persisted in new format. */
  targetInputIndex?: number
  /** Legacy: used when loading old snapshots; resolved to targetInputIndex in loader. */
  targetInputName?: string
  /** Which output handle the edge is drawn from: 'output', 'output-top', 'output-bottom'. Optional; default 'output'. */
  sourceHandle?: string
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
      (no.type !== 'computation' && no.type !== 'presentation' && no.type !== 'file')
    )
      return null
    const pos = no.position
    if (pos == null || typeof pos !== 'object' || typeof (pos as { x?: unknown }).x !== 'number' || typeof (pos as { y?: unknown }).y !== 'number')
      return null
    const inputs = no.inputs
    const parsedInputs: ProjectNodeInput[] | undefined =
      Array.isArray(inputs) && inputs.length > 0
        ? inputs
            .filter(
              (i): i is ProjectNodeInput =>
                i != null &&
                typeof i === 'object' &&
                typeof (i as ProjectNodeInput).name === 'string' &&
                typeof (i as ProjectNodeInput).type === 'string',
            )
            .map((i) => ({ name: (i as ProjectNodeInput).name, type: (i as ProjectNodeInput).type }))
        : undefined
    parsedNodes.push({
      id: no.id,
      position: { x: (pos as { x: number }).x, y: (pos as { y: number }).y },
      type: no.type as ProjectNodeType,
      content: typeof no.content === 'string' ? no.content : undefined,
      inputs: parsedInputs,
      ...(no.type === 'file' && typeof no.url === 'string' ? { url: no.url } : {}),
    })
  }
  const parsedEdges: ProjectEdge[] = []
  for (const e of edges) {
    if (e == null || typeof e !== 'object') return null
    const eo = e as Record<string, unknown>
    if (typeof eo.sourceId !== 'string' || typeof eo.targetId !== 'string') return null
    const hasIndex = typeof eo.targetInputIndex === 'number'
    const hasName = typeof eo.targetInputName === 'string'
    if (!hasIndex && !hasName) return null
    const edge: ProjectEdge = {
      sourceId: eo.sourceId,
      targetId: eo.targetId,
      ...(hasIndex ? { targetInputIndex: eo.targetInputIndex as number } : {}),
      ...(hasName ? { targetInputName: eo.targetInputName as string } : {}),
    }
    if (typeof eo.sourceHandle === 'string') edge.sourceHandle = eo.sourceHandle
    parsedEdges.push(edge)
  }
  return {
    id,
    version: typeof o.version === 'number' ? o.version : undefined,
    nodes: parsedNodes,
    edges: parsedEdges,
  }
}
