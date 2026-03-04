/**
 * React Flow wrapper: reads nodes/edges from graph store, custom node types (computation, presentation).
 * Handles edge creation (optimistic + snaqlite/graph/connect; on error clear pending + toast)
 * and edge deletion (onEdgesDelete → disconnectEdge + LSP disconnect).
 * Exposes getViewportCenter() via ref for placing new nodes at the visible center.
 */

import type { Ref, RefObject, MouseEvent, MutableRefObject, DragEvent } from 'react'
import { useCallback, useEffect, useImperativeHandle, useMemo, useRef, useState } from 'react'
import {
  ReactFlow,
  Background,
  Controls,
  useReactFlow,
  ConnectionMode,
  type Connection,
  type Node,
  type Edge,
  type NodeChange,
  type OnSelectionChangeFunc,
} from '@xyflow/react'
import { connectEdge, disconnectEdge } from './edge-handlers'
import { COMPUTATION_OUTPUT_HANDLE_RIGHT } from '~/lib/constants'
import { applyDisconnectForDeletedEdges } from './edge-delete-params'
import { getDragHandleSelector } from './graph-drag-handle'
import { applyNodePositionChanges } from './graph-node-position-changes'
import { graphEdgeToFlowEdge } from './graph-edge-utils'
import { getFlowNodeData } from './graph-node-data'
import { ComputationBoxNode } from './computation-box-node'
import { FileBlockNode } from './file-block-node'
import { PresentationBlockNode } from './presentation-block-node'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { registerBlobUrl } from '~/lib/blob-url-cache'
import { putFileBlob } from '~/lib/file-blob-idb'
import { useGraphStore } from '~/store'

function graphNodeToFlowNode(
  n: import('~/store').GraphNode,
  storeNodes: import('~/store').GraphNode[],
  storeEdges: import('~/store').GraphEdge[],
): Node {
  const data = getFlowNodeData(n, storeNodes, storeEdges)
  return {
    id: n.id,
    type: n.type,
    position: n.position,
    data: data as unknown as Record<string, unknown>,
  }
}

export interface GraphCanvasProps {
  /** Current project ID (for persisting dropped file blobs to IndexedDB). */
  projectId: string
  onSelectionChange?: OnSelectionChangeFunc
  /** Synced into node.selected so React Flow selection matches app state (e.g. toolbar Delete). */
  selectedNodeIds?: string[]
  /** Synced into edge.selected and edge style so selected edges show accent color (match node border). */
  selectedEdgeIds?: string[]
  /** Ref to get viewport center (flow coords) for placing new nodes. */
  viewportRef?: Ref<GraphCanvasViewportRef | null>
}

export interface GraphCanvasViewportRef {
  /** Flow coordinates of the center of the visible viewport (for placing new nodes). */
  getViewportCenter: () => { x: number; y: number } | null
}

type ScreenToFlowPositionFn = (position: { x: number; y: number }) => { x: number; y: number }

/** Must be rendered inside ReactFlow. Exposes getViewportCenter via the forwarded ref and keeps screenToFlowPositionRef for drop. */
function ViewportCenterRef({
  viewportRef,
  forwardedRef,
  screenToFlowPositionRef,
}: {
  viewportRef: RefObject<HTMLDivElement | null>
  forwardedRef: Ref<GraphCanvasViewportRef | null>
  screenToFlowPositionRef: MutableRefObject<ScreenToFlowPositionFn | null>
}) {
  const { screenToFlowPosition } = useReactFlow()
  useEffect(() => {
    screenToFlowPositionRef.current = screenToFlowPosition
    return () => {
      screenToFlowPositionRef.current = null
    }
  }, [screenToFlowPosition, screenToFlowPositionRef])
  useImperativeHandle(
    forwardedRef,
    () => ({
      getViewportCenter: () => {
        const el = viewportRef.current
        if (!el) return null
        const rect = el.getBoundingClientRect()
        const center = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 }
        return screenToFlowPosition(center)
      },
    }),
    [screenToFlowPosition, viewportRef],
  )
  return null
}

export function GraphCanvas(props: GraphCanvasProps) {
  const { projectId, onSelectionChange, selectedNodeIds = [], selectedEdgeIds = [] } = props
  const viewportRef = useRef<HTMLDivElement>(null)
  const screenToFlowPositionRef = useRef<ScreenToFlowPositionFn | null>(null) as MutableRefObject<ScreenToFlowPositionFn | null>
  const addNode = useGraphStore((s) => s.addNode)
  const onSelectionChangeRef = useRef(onSelectionChange)
  onSelectionChangeRef.current = onSelectionChange

  const onDragOver = useCallback((e: DragEvent<HTMLDivElement>) => {
    if (e.dataTransfer.types.includes('Files')) {
      e.preventDefault()
      e.dataTransfer.dropEffect = 'copy'
    }
  }, [])

  const onDrop = useCallback(
    (e: DragEvent<HTMLDivElement>) => {
      if (!e.dataTransfer.types.includes('Files')) return
      e.preventDefault()
      const files = e.dataTransfer.files
      if (!files?.length) return
      const position = screenToFlowPositionRef.current?.({ x: e.clientX, y: e.clientY })
      if (!position) return
      const id = crypto.randomUUID()
      const file = files[0]
      const url = URL.createObjectURL(file)
      registerBlobUrl(url, file)
      addNode({
        id,
        position,
        type: 'file',
        uri: nodeIdToUri(id),
        url,
        fileType: file.type || undefined,
      })
      void putFileBlob(projectId, id, file).catch((err) => {
        console.error('[GraphCanvas] Failed to persist file blob to IndexedDB', err)
      })
      onSelectionChangeRef.current?.({
        nodes: [{ id, position, data: {}, type: 'file' }],
        edges: [],
      })
    },
    [addNode, projectId],
  )

  const nodeTypes = useMemo(
    () =>
      ({
        computation: ComputationBoxNode,
        presentation: PresentationBlockNode,
        file: FileBlockNode,
      }) as const,
    [],
  )
  const storeNodes = useGraphStore((s) => s.nodes)
  const storeEdges = useGraphStore((s) => s.edges)
  const moveNode = useGraphStore((s) => s.moveNode)
  /** Live positions during drag so the node follows the pointer until drop. */
  const [livePositions, setLivePositions] = useState<Record<string, { x: number; y: number }>>({})

  const nodes = useMemo(() => {
    const set = new Set(selectedNodeIds)
    return storeNodes.map((n) => {
      const position = livePositions[n.id] ?? n.position
      return {
        ...graphNodeToFlowNode(n, storeNodes, storeEdges),
        position,
        selected: set.has(n.id),
        dragHandle: getDragHandleSelector(n.type),
      }
    })
  }, [storeNodes, storeEdges, selectedNodeIds, livePositions])
  const selectedEdgeIdSet = useMemo(() => new Set(selectedEdgeIds), [selectedEdgeIds])
  const edges = useMemo(() => {
    return storeEdges.map((e) => {
      const edge = graphEdgeToFlowEdge(e)
      const selected = selectedEdgeIdSet.has(edge.id)
      return {
        ...edge,
        selected,
        style: selected
          ? { stroke: 'var(--accent)', strokeWidth: 2 }
          : undefined,
      }
    })
  }, [storeEdges, selectedEdgeIdSet])

  const onConnect = useCallback(
    async (connection: Connection) => {
      if (!connection.source || !connection.target || connection.targetHandle == null) return
      const targetInputIndex = Number(connection.targetHandle)
      if (!Number.isInteger(targetInputIndex) || targetInputIndex < 0) return
      const sourceNode = useGraphStore.getState().nodes.find((n) => n.id === connection.source)
      const targetNode = useGraphStore.getState().nodes.find((n) => n.id === connection.target)
      if (!sourceNode || !targetNode) return
      await connectEdge(
        sourceNode.uri,
        targetNode.uri,
        targetInputIndex,
        connection.sourceHandle ?? COMPUTATION_OUTPUT_HANDLE_RIGHT,
      )
    },
    [],
  )

  const onNodesChange = useCallback(
    (changes: NodeChange[]) => {
      applyNodePositionChanges(changes, moveNode, setLivePositions)
    },
    [moveNode],
  )

  const onEdgesDelete = useCallback((deleted: Edge[]) => {
    const nodes = useGraphStore.getState().nodes
    applyDisconnectForDeletedEdges(
      deleted.map((e) => ({ target: e.target, targetHandle: e.targetHandle })),
      nodes.map((n) => ({ id: n.id, uri: n.uri })),
      (uri, index) => void disconnectEdge(uri, index),
    )
  }, [])

  /** When a node is clicked, set selection to that node so the parent state stays in sync. */
  const onNodeClick = useCallback(
    (_: MouseEvent, node: Node) => {
      if (typeof window !== 'undefined' && (window as Window & { __E2E_DEBUG_CLICKS__?: boolean }).__E2E_DEBUG_CLICKS__) {
        (window as Window & { __E2E_LAST_CLICK__?: string }).__E2E_LAST_CLICK__ = 'node'
      }
      onSelectionChange?.({ nodes: [node], edges: [] })
    },
    [onSelectionChange],
  )

  /** When the pane is clicked (empty space), clear selection. */
  const onPaneClick = useCallback(() => {
    if (typeof window !== 'undefined' && (window as Window & { __E2E_DEBUG_CLICKS__?: boolean }).__E2E_DEBUG_CLICKS__) {
      (window as Window & { __E2E_LAST_CLICK__?: string }).__E2E_LAST_CLICK__ = 'pane'
    }
    onSelectionChange?.({ nodes: [], edges: [] })
  }, [onSelectionChange])

  /** When an edge is clicked, sync selection to parent so Delete/Backspace can remove it. */
  const onEdgeClick = useCallback(
    (_: MouseEvent, edge: Edge) => {
      onSelectionChange?.({ nodes: [], edges: [edge] })
    },
    [onSelectionChange],
  )

  return (
    <div
      ref={viewportRef}
      style={{ width: '100%', height: '100%', background: 'var(--bg-primary)' }}
    >
      <ReactFlow
        nodes={nodes}
        edges={edges}
        connectionMode={ConnectionMode.Loose}
        connectionRadius={40}
        connectOnClick
        onNodesChange={onNodesChange}
        onConnect={onConnect}
        onEdgesDelete={onEdgesDelete}
        onSelectionChange={onSelectionChange}
        onNodeClick={onNodeClick}
        onEdgeClick={onEdgeClick}
        onPaneClick={onPaneClick}
        onDragOver={onDragOver}
        onDrop={onDrop}
        nodeTypes={nodeTypes}
        nodesDraggable
        defaultEdgeOptions={{ selectable: true, deletable: true }}
        fitView
        fitViewOptions={{ padding: 0.2, maxZoom: 1.2 }}
      >
        <ViewportCenterRef
          viewportRef={viewportRef}
          forwardedRef={props.viewportRef ?? null}
          screenToFlowPositionRef={screenToFlowPositionRef}
        />
        <Background />
        <Controls />
      </ReactFlow>
    </div>
  )
}
