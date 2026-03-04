/**
 * Graph state: nodes (id, position, type, uri), edges, pending edge.
 * applyNodeSignature(uri, inputs, outputType) updates port info from LSP nodeSignatureUpdated.
 * Undo/redo: last UNDO_STACK_MAX states (nodes + edges); getter supplies current state with Monaco content.
 */

import { create } from 'zustand'
import {
  type ComputationOutputHandleId,
  COMPUTATION_OUTPUT_HANDLE_RIGHT,
  UNDO_STACK_MAX,
} from '~/lib/constants'
import { unregisterBlobUrl } from '~/lib/blob-url-cache'
import type { NodeInputPort } from '~/lsp/types'

export type UndoSnapshot = { nodes: GraphNode[]; edges: GraphEdge[] }

function pushUndoAndClearRedo(
  getter: (() => UndoSnapshot) | null,
  currentUndoStack: UndoSnapshot[],
): UndoSnapshot[] {
  if (!getter) return currentUndoStack
  try {
    const snapshot = getter()
    const cloned = JSON.parse(JSON.stringify(snapshot)) as UndoSnapshot
    return [cloned, ...currentUndoStack].slice(0, UNDO_STACK_MAX)
  } catch {
    return currentUndoStack
  }
}

export type NodeType = 'computation' | 'presentation' | 'file'

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
  /** URL for file nodes (blob URL, data URL, or https). Optional; used when type === 'file'. */
  url?: string
  /** MIME type for file nodes (e.g. from dropped File). Optional; used when type === 'file'. */
  fileType?: string
}

export interface GraphEdge {
  sourceId: string
  targetId: string
  /** Index of the target node's input port (0-based). Connections survive input renames. */
  targetInputIndex: number
  /** Which output handle the edge is drawn from: right, top, or bottom. Default right. */
  sourceHandle?: ComputationOutputHandleId
}

export interface PendingEdge {
  sourceId: string
  sourceHandle: string | null
  targetPosition: { x: number; y: number } | null
}

export type UndoSnapshotGetter = (() => UndoSnapshot) | null

interface GraphState {
  nodes: GraphNode[]
  edges: GraphEdge[]
  pendingEdge: PendingEdge | null
  /** When set, the computation box editor for this node id should focus when it mounts. Cleared after focus or on setGraph. */
  focusEditorForNodeId: string | null
  undoStack: UndoSnapshot[]
  redoStack: UndoSnapshot[]
  /** Set from canvas on mount; cleared on unmount. Used to capture current state (with Monaco content) before user-driven mutations. */
  undoSnapshotGetter: UndoSnapshotGetter
  addNode: (node: Omit<GraphNode, 'inputs' | 'outputType'>) => void
  moveNode: (id: string, position: { x: number; y: number }) => void
  removeNode: (id: string) => void
  addEdge: (edge: Omit<GraphEdge, 'sourceHandle'> & { sourceHandle?: string }) => void
  removeEdge: (targetId: string, targetInputIndex: number) => void
  setPendingEdge: (edge: PendingEdge | null) => void
  clearPendingEdge: () => void
  setFocusEditorForNodeId: (id: string | null) => void
  /** Updates only outputType from LSP. Inputs are block properties edited in the UI, not from block text. */
  applyNodeSignature: (uri: string, _inputs: NodeInputPort[], outputType?: string | null) => void
  setNodeInputs: (nodeId: string, inputs: NodeInputPort[]) => void
  /** Updates computation node's initialContent (e.g. when editor content changes). Used so connectEdge has latest content when target editor may be unmounted. Does not push undo. */
  setNodeContent: (nodeId: string, content: string) => void
  /** Replace entire graph (e.g. when loading a project). Clears pendingEdge and focusEditorForNodeId. */
  setGraph: (nodes: GraphNode[], edges: GraphEdge[], options?: { clearHistory?: boolean }) => void
  setUndoSnapshotGetter: (getter: UndoSnapshotGetter) => void
  undo: () => void
  redo: () => void
}

export const useGraphStore = create<GraphState>((set) => ({
  nodes: [],
  edges: [],
  pendingEdge: null,
  focusEditorForNodeId: null,
  undoStack: [],
  redoStack: [],
  undoSnapshotGetter: null,

  addNode: (node) =>
    set((state) => {
      const undoStack = pushUndoAndClearRedo(state.undoSnapshotGetter, state.undoStack)
      return {
        nodes: [...state.nodes, { ...node, inputs: undefined, outputType: undefined }],
        focusEditorForNodeId:
          node.type === 'computation' ? node.id : state.focusEditorForNodeId,
        undoStack,
        redoStack: [],
      }
    }),

  moveNode: (id, position) =>
    set((state) => {
      const undoStack = pushUndoAndClearRedo(state.undoSnapshotGetter, state.undoStack)
      return {
        nodes: state.nodes.map((n) => (n.id === id ? { ...n, position } : n)),
        undoStack,
        redoStack: [],
      }
    }),

  removeNode: (id) =>
    set((state) => {
      const node = state.nodes.find((n) => n.id === id)
      if (node?.type === 'file' && node.url?.startsWith('blob:')) {
        unregisterBlobUrl(node.url)
        try {
          URL.revokeObjectURL(node.url)
        } catch {
          // ignore
        }
      }
      const undoStack = pushUndoAndClearRedo(state.undoSnapshotGetter, state.undoStack)
      return {
        nodes: state.nodes.filter((n) => n.id !== id),
        edges: state.edges.filter((e) => e.sourceId !== id && e.targetId !== id),
        undoStack,
        redoStack: [],
      }
    }),

  addEdge: (edge) =>
    set((state) => {
      const undoStack = pushUndoAndClearRedo(state.undoSnapshotGetter, state.undoStack)
      const fullEdge: GraphEdge = {
        ...edge,
        sourceHandle: edge.sourceHandle ?? COMPUTATION_OUTPUT_HANDLE_RIGHT,
      }
      return {
        edges: state.edges.filter(
          (e) => !(e.targetId === edge.targetId && e.targetInputIndex === edge.targetInputIndex),
        ).concat(fullEdge),
        pendingEdge: null,
        undoStack,
        redoStack: [],
      }
    }),

  removeEdge: (targetId, targetInputIndex) =>
    set((state) => {
      const undoStack = pushUndoAndClearRedo(state.undoSnapshotGetter, state.undoStack)
      return {
        edges: state.edges.filter(
          (e) => !(e.targetId === targetId && e.targetInputIndex === targetInputIndex),
        ),
        undoStack,
        redoStack: [],
      }
    }),

  setPendingEdge: (pendingEdge) => set({ pendingEdge }),

  clearPendingEdge: () => set({ pendingEdge: null }),

  setFocusEditorForNodeId: (focusEditorForNodeId) => set({ focusEditorForNodeId }),

  applyNodeSignature: (uri, _inputs, outputType) =>
    set((state) => {
      const node = state.nodes.find((n) => n.uri === uri)
      const nextOutput = outputType ?? null
      if (!node || node.outputType === nextOutput) return state
      return {
        nodes: state.nodes.map((n) =>
          n.uri === uri ? { ...n, outputType: nextOutput } : n,
        ),
      }
    }),

  setNodeInputs: (nodeId, inputs) =>
    set((state) => {
      const undoStack = pushUndoAndClearRedo(state.undoSnapshotGetter, state.undoStack)
      return {
        nodes: state.nodes.map((n) => (n.id === nodeId ? { ...n, inputs } : n)),
        undoStack,
        redoStack: [],
      }
    }),

  setNodeContent: (nodeId, content) =>
    set((state) => ({
      nodes: state.nodes.map((n) =>
        n.id === nodeId && n.type === 'computation' ? { ...n, initialContent: content } : n,
      ),
    })),

  setGraph: (nodes, edges, options) =>
    set((_state) => ({
      nodes,
      edges,
      pendingEdge: null,
      focusEditorForNodeId: null,
      ...(options?.clearHistory ? { undoStack: [], redoStack: [] } : {}),
    })),

  setUndoSnapshotGetter: (undoSnapshotGetter) => set({ undoSnapshotGetter }),

  undo: () =>
    set((state) => {
      if (state.undoStack.length === 0) return state
      const [prev, ...restUndo] = state.undoStack
      const redoEntry: UndoSnapshot = JSON.parse(
        JSON.stringify({ nodes: state.nodes, edges: state.edges }),
      )
      return {
        nodes: prev.nodes,
        edges: prev.edges,
        undoStack: restUndo,
        redoStack: [...state.redoStack, redoEntry],
      }
    }),

  redo: () =>
    set((state) => {
      if (state.redoStack.length === 0) return state
      const next = state.redoStack[state.redoStack.length - 1]
      const restRedo = state.redoStack.slice(0, -1)
      const undoEntry: UndoSnapshot = JSON.parse(
        JSON.stringify({ nodes: state.nodes, edges: state.edges }),
      )
      return {
        nodes: next.nodes,
        edges: next.edges,
        undoStack: [...state.undoStack, undoEntry],
        redoStack: restRedo,
      }
    }),
}))
