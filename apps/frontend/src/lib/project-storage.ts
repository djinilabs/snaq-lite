/**
 * LocalStorage persistence for projects index and per-project snapshots.
 * Serialization builds ProjectSnapshot from graph store state and Monaco model content.
 */

import { getModel } from '~/editor/text-model-registry'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { COMPUTATION_OUTPUT_HANDLE_RIGHT } from '~/lib/constants'
import type { GraphEdge, GraphNode } from '~/store'
import type { ProjectSnapshot } from '~/types/project'
import { parseProjectSnapshot } from '~/types/project'

/** Storage keys; exported for tests and shared usage. */
export const PROJECTS_INDEX_KEY = 'snaq-projects-index'
export const PROJECT_KEY_PREFIX = 'snaq-project-'

export interface ProjectMeta {
  id: string
  name?: string
  updatedAt?: number
}

export function getProjectsIndex(): ProjectMeta[] {
  try {
    const raw = localStorage.getItem(PROJECTS_INDEX_KEY)
    if (!raw) return []
    const parsed = JSON.parse(raw) as unknown
    if (!Array.isArray(parsed)) return []
    return parsed.filter(
      (p): p is ProjectMeta =>
        p != null && typeof p === 'object' && typeof (p as ProjectMeta).id === 'string',
    )
  } catch {
    return []
  }
}

export function setProjectsIndex(meta: ProjectMeta[]): void {
  localStorage.setItem(PROJECTS_INDEX_KEY, JSON.stringify(meta))
}

export function getProjectSnapshot(projectId: string): ProjectSnapshot | null {
  try {
    const raw = localStorage.getItem(PROJECT_KEY_PREFIX + projectId)
    if (!raw) return null
    return parseProjectSnapshot(JSON.parse(raw))
  } catch {
    return null
  }
}

export function setProjectSnapshot(snapshot: ProjectSnapshot): void {
  localStorage.setItem(PROJECT_KEY_PREFIX + snapshot.id, JSON.stringify(snapshot))
}

export function deleteProjectSnapshot(projectId: string): void {
  localStorage.removeItem(PROJECT_KEY_PREFIX + projectId)
}

/**
 * Build a ProjectSnapshot from current graph nodes and edges.
 * Node content comes from Monaco model if present, else node.initialContent or ''.
 */
export function buildSnapshotFromGraph(
  projectId: string,
  nodes: GraphNode[],
  edges: GraphEdge[],
): ProjectSnapshot {
  const projectNodes = nodes.map((n) => {
    const model = getModel(nodeIdToUri(n.id), undefined as never)
    const content = model ? model.getValue() : n.initialContent ?? ''
    const base = {
      id: n.id,
      position: n.position,
      type: n.type,
    }
    if (n.type === 'file') return { ...base, ...(n.url ? { url: n.url } : {}) }
    if (n.type !== 'computation') return base
    return {
      ...base,
      ...(content ? { content } : {}),
      ...(n.inputs && n.inputs.length > 0 ? { inputs: n.inputs } : {}),
    }
  })
  return {
    id: projectId,
    version: 1,
    nodes: projectNodes,
    edges: edges.map((e) => ({
      sourceId: e.sourceId,
      targetId: e.targetId,
      targetInputIndex: e.targetInputIndex,
      ...(e.sourceHandle != null && e.sourceHandle !== COMPUTATION_OUTPUT_HANDLE_RIGHT
        ? { sourceHandle: e.sourceHandle }
        : {}),
    })),
  }
}

/**
 * Build graph state for undo stack: deep-cloned nodes with initialContent from Monaco model for computation nodes, and copy of edges.
 */
export function getGraphStateForUndo(
  nodes: GraphNode[],
  edges: GraphEdge[],
): { nodes: GraphNode[]; edges: GraphEdge[] } {
  const nodesWithContent = nodes.map((n) => {
    const content =
      n.type === 'computation'
        ? getModel(nodeIdToUri(n.id), undefined as never)?.getValue() ?? n.initialContent ?? ''
        : n.initialContent ?? ''
    return { ...n, initialContent: content }
  })
  const clonedNodes = JSON.parse(JSON.stringify(nodesWithContent)) as GraphNode[]
  const clonedEdges = JSON.parse(JSON.stringify(edges)) as GraphEdge[]
  return { nodes: clonedNodes, edges: clonedEdges }
}

/**
 * Sync Monaco models to match the given nodes' initialContent (e.g. after undo/redo).
 */
export function syncModelsToGraphNodes(nodes: GraphNode[]): void {
  for (const n of nodes) {
    if (n.type !== 'computation') continue
    const model = getModel(nodeIdToUri(n.id), undefined as never)
    if (model) model.setValue(n.initialContent ?? '')
  }
}
