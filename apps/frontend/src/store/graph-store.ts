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
  /** Initial block content when loading a project; Monaco is source of truth after first edit. */
  initialContent?: string
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
  /** When set, the computation box editor for this node id should focus when it mounts. Cleared after focus or on setGraph. */
  focusEditorForNodeId: string | null
  addNode: (node: Omit<GraphNode, 'inputs' | 'outputType'>) => void
  moveNode: (id: string, position: { x: number; y: number }) => void
  removeNode: (id: string) => void
  addEdge: (edge: GraphEdge) => void
  removeEdge: (targetId: string, targetInputName: string) => void
  setPendingEdge: (edge: PendingEdge | null) => void
  clearPendingEdge: () => void
  setFocusEditorForNodeId: (id: string | null) => void
  /** Updates only outputType from LSP. Inputs are block properties edited in the UI, not from block text. */
  applyNodeSignature: (uri: string, _inputs: NodeInputPort[], outputType?: string | null) => void
  setNodeInputs: (nodeId: string, inputs: NodeInputPort[]) => void
  /** Replace entire graph (e.g. when loading a project). Clears pendingEdge and focusEditorForNodeId. */
  setGraph: (nodes: GraphNode[], edges: GraphEdge[]) => void
}

export const useGraphStore = create<GraphState>((set) => ({
  nodes: [],
  edges: [],
  pendingEdge: null,
  focusEditorForNodeId: null,

  addNode: (node) =>
    set((state) => ({
      nodes: [...state.nodes, { ...node, inputs: undefined, outputType: undefined }],
      focusEditorForNodeId:
        node.type === 'computation' ? node.id : state.focusEditorForNodeId,
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

  setFocusEditorForNodeId: (focusEditorForNodeId) => set({ focusEditorForNodeId }),

  applyNodeSignature: (uri, _inputs, outputType) =>
    set((state) => ({
      nodes: state.nodes.map((n) =>
        n.uri === uri ? { ...n, outputType: outputType ?? null } : n,
      ),
    })),

  setNodeInputs: (nodeId, inputs) =>
    set((state) => ({
      nodes: state.nodes.map((n) => (n.id === nodeId ? { ...n, inputs } : n)),
    })),

  setGraph: (nodes, edges) =>
    set({ nodes, edges, pendingEdge: null, focusEditorForNodeId: null }),
}))
