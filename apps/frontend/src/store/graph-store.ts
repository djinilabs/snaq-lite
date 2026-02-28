/**
 * Graph state: nodes (id, position, type, uri), edges, pending edge.
 * applyNodeSignature(uri, inputs, outputType) updates port info from LSP nodeSignatureUpdated.
 */

import { create } from 'zustand'
import type { NodeInputPort } from '~/lsp/types'

export type NodeType = 'computation' | 'presentation'

export interface GraphNode {
  id: string
  position: { x: number; y: number }
  type: NodeType
  /** Virtual document URI, e.g. snaq://graph/<id>.sl */
  uri: string
  /** From LSP nodeSignatureUpdated */
  inputs?: NodeInputPort[]
  outputType?: string | null
}

export interface GraphEdge {
  sourceId: string
  targetId: string
  targetInputName: string
}

export interface PendingEdge {
  sourceId: string
  sourceHandle: string | null
  targetPosition: { x: number; y: number } | null
}

interface GraphState {
  nodes: GraphNode[]
  edges: GraphEdge[]
  pendingEdge: PendingEdge | null
  addNode: (node: Omit<GraphNode, 'inputs' | 'outputType'>) => void
  moveNode: (id: string, position: { x: number; y: number }) => void
  removeNode: (id: string) => void
  addEdge: (edge: GraphEdge) => void
  removeEdge: (targetId: string, targetInputName: string) => void
  setPendingEdge: (edge: PendingEdge | null) => void
  clearPendingEdge: () => void
  applyNodeSignature: (uri: string, inputs: NodeInputPort[], outputType?: string | null) => void
}

export const useGraphStore = create<GraphState>((set) => ({
  nodes: [],
  edges: [],
  pendingEdge: null,

  addNode: (node) =>
    set((state) => ({
      nodes: [...state.nodes, { ...node, inputs: undefined, outputType: undefined }],
    })),

  moveNode: (id, position) =>
    set((state) => ({
      nodes: state.nodes.map((n) => (n.id === id ? { ...n, position } : n)),
    })),

  removeNode: (id) =>
    set((state) => ({
      nodes: state.nodes.filter((n) => n.id !== id),
      edges: state.edges.filter((e) => e.sourceId !== id && e.targetId !== id),
    })),

  addEdge: (edge) =>
    set((state) => ({
      edges: state.edges.filter(
        (e) => !(e.targetId === edge.targetId && e.targetInputName === edge.targetInputName),
      ).concat(edge),
      pendingEdge: null,
    })),

  removeEdge: (targetId, targetInputName) =>
    set((state) => ({
      edges: state.edges.filter(
        (e) => !(e.targetId === targetId && e.targetInputName === targetInputName),
      ),
    })),

  setPendingEdge: (pendingEdge) => set({ pendingEdge }),

  clearPendingEdge: () => set({ pendingEdge: null }),

  applyNodeSignature: (uri, inputs, outputType) =>
    set((state) => ({
      nodes: state.nodes.map((n) =>
        n.uri === uri ? { ...n, inputs, outputType: outputType ?? null } : n,
      ),
    })),
}))
