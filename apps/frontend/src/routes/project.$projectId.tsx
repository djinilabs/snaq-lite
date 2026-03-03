import { useCallback, useEffect, useMemo, useRef, useState } from 'react'
import { createFileRoute } from '@tanstack/react-router'
import { GraphCanvas, type GraphCanvasViewportRef } from '~/components/canvas/graph-canvas'
import { applyDisconnectForDeletedEdges } from '~/components/canvas/edge-delete-params'
import { disconnectEdge } from '~/components/canvas/edge-handlers'
import { ProjectToolbar } from '~/components/project-toolbar'
import { AutoSaveContext } from '~/contexts/auto-save-context'
import { useProjectLoader } from '~/hooks/use-project-loader'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { AUTO_SAVE_DEBOUNCE_MS } from '~/lib/constants'
import { buildSnapshotFromGraph, getGraphStateForUndo, setProjectSnapshot } from '~/lib/project-storage'
import { performRedo, performUndo } from '~/lib/perform-undo-redo'
import { useGraphStore } from '~/store'
import { useProjectsIndexStore } from '~/store'

/** Selected edge shape for keyboard delete (target + targetHandle from React Flow). */
type SelectedEdgeLike = { target: string; targetHandle?: string | null }

export const Route = createFileRoute('/project/$projectId')({
  component: ProjectCanvasPage,
})

function ProjectCanvasPage() {
  const { projectId } = Route.useParams()
  useProjectLoader(projectId)
  const canvasViewportRef = useRef<GraphCanvasViewportRef | null>(null)
  const [selectedNodeIds, setSelectedNodeIds] = useState<string[]>([])
  /** Selected edge IDs for visual highlight; ref used by keydown so Delete works before state update. */
  const [selectedEdgeIds, setSelectedEdgeIds] = useState<string[]>([])
  const selectedEdgesRef = useRef<SelectedEdgeLike[]>([])
  const nodes = useGraphStore((s) => s.nodes)
  const edges = useGraphStore((s) => s.edges)
  const addNode = useGraphStore((s) => s.addNode)
  const removeNode = useGraphStore((s) => s.removeNode)
  const setUndoSnapshotGetter = useGraphStore((s) => s.setUndoSnapshotGetter)

  const performSave = useCallback(() => {
    const state = useGraphStore.getState()
    const snapshot = buildSnapshotFromGraph(projectId, state.nodes, state.edges)
    setProjectSnapshot(snapshot)
    const projectsState = useProjectsIndexStore.getState().projects
    const updated = projectsState.map((p) =>
      p.id === projectId ? { ...p, updatedAt: Date.now() } : p,
    )
    useProjectsIndexStore.getState().setProjects(updated)
  }, [projectId])

  const saveTimeoutRef = useRef<ReturnType<typeof setTimeout> | null>(null)
  const requestSave = useCallback(() => {
    if (saveTimeoutRef.current) clearTimeout(saveTimeoutRef.current)
    saveTimeoutRef.current = setTimeout(() => {
      saveTimeoutRef.current = null
      performSave()
    }, AUTO_SAVE_DEBOUNCE_MS)
  }, [performSave])

  const autoSaveValue = useMemo<AutoSaveContextValue>(() => ({ requestSave }), [requestSave])

  useEffect(() => {
    requestSave()
  }, [nodes, edges, requestSave])

  useEffect(() => {
    const getter = () => {
      const state = useGraphStore.getState()
      return getGraphStateForUndo(state.nodes, state.edges)
    }
    setUndoSnapshotGetter(getter)
    return () => {
      setUndoSnapshotGetter(null)
      if (saveTimeoutRef.current) {
        clearTimeout(saveTimeoutRef.current)
        saveTimeoutRef.current = null
      }
    }
  }, [setUndoSnapshotGetter])

  useEffect(() => {
    const onKeyDown = (e: KeyboardEvent) => {
      if ((e.ctrlKey || e.metaKey) && e.key === 'z') {
        e.preventDefault()
        if (e.shiftKey) {
          performRedo()
        } else {
          performUndo()
        }
      }
    }
    window.addEventListener('keydown', onKeyDown)
    return () => window.removeEventListener('keydown', onKeyDown)
  }, [])

  const handleAddNode = useCallback(
    (type: 'computation' | 'presentation' | 'file') => {
      const id = crypto.randomUUID()
      const center = canvasViewportRef.current?.getViewportCenter()
      // Offset so node center (not top-left) is at viewport center; fallback if ref not ready
      const NODE_OFFSET_X = 130
      const NODE_OFFSET_Y = 60
      const position = center
        ? { x: center.x - NODE_OFFSET_X, y: center.y - NODE_OFFSET_Y }
        : { x: 150 + nodes.length * 30, y: 100 + nodes.length * 40 }
      addNode({ id, position, type, uri: nodeIdToUri(id) })
      setSelectedNodeIds([id])
    },
    [addNode, nodes.length],
  )

  const handleDeleteSelected = useCallback(() => {
    for (const id of selectedNodeIds) {
      removeNode(id)
    }
    setSelectedNodeIds([])
  }, [selectedNodeIds, removeNode])

  const handleSelectionChange = useCallback(
    (params: { nodes: { id: string }[]; edges?: { id: string; target: string; targetHandle?: string | null }[] }) => {
      setSelectedNodeIds(params.nodes.map((n) => n.id))
      const edgeList = params.edges ?? []
      setSelectedEdgeIds(edgeList.map((e) => e.id))
      selectedEdgesRef.current = edgeList.map((e) => ({ target: e.target, targetHandle: e.targetHandle }))
    },
    [],
  )

  const handleDeleteSelectedEdges = useCallback((edgesToDelete: SelectedEdgeLike[]) => {
    const storeNodes = useGraphStore.getState().nodes
    const nodeLike = storeNodes.map((n) => ({ id: n.id, uri: n.uri }))
    applyDisconnectForDeletedEdges(edgesToDelete, nodeLike, (uri, index) => void disconnectEdge(uri, index))
    setSelectedEdgeIds([])
    selectedEdgesRef.current = []
  }, [])

  useEffect(() => {
    const onKeyDown = (e: KeyboardEvent) => {
      if (e.key !== 'Delete' && e.key !== 'Backspace') return
      const edges = selectedEdgesRef.current
      if (edges.length > 0) {
        e.preventDefault()
        handleDeleteSelectedEdges(edges)
        return
      }
      if (selectedNodeIds.length > 0) {
        e.preventDefault()
        handleDeleteSelected()
      }
    }
    window.addEventListener('keydown', onKeyDown)
    return () => window.removeEventListener('keydown', onKeyDown)
  }, [selectedNodeIds.length, handleDeleteSelectedEdges, handleDeleteSelected])

  return (
    <AutoSaveContext.Provider value={autoSaveValue}>
      <div
        data-testid="canvas-page"
        style={{
          display: 'flex',
          flexDirection: 'column',
          width: '100vw',
          height: '100vh',
          background: 'var(--bg-primary)',
        }}
      >
        <ProjectToolbar
          projectId={projectId}
          onAddNode={handleAddNode}
          onDeleteSelected={handleDeleteSelected}
          hasSelection={selectedNodeIds.length > 0}
        />
        <div data-testid="graph-canvas-wrapper" style={{ flex: 1, minHeight: 0 }}>
          <GraphCanvas
            viewportRef={canvasViewportRef}
            selectedNodeIds={selectedNodeIds}
            selectedEdgeIds={selectedEdgeIds}
            onSelectionChange={handleSelectionChange}
          />
        </div>
      </div>
    </AutoSaveContext.Provider>
  )
}
