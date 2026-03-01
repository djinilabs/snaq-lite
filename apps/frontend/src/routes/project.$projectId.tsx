import { useState, useCallback, useEffect, useRef } from 'react'
import { createFileRoute } from '@tanstack/react-router'
import { GraphCanvas, type GraphCanvasViewportRef } from '~/components/canvas/graph-canvas'
import { ProjectToolbar } from '~/components/project-toolbar'
import { useProjectLoader } from '~/hooks/use-project-loader'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { useGraphStore } from '~/store'

export const Route = createFileRoute('/project/$projectId')({
  component: ProjectCanvasPage,
})

function ProjectCanvasPage() {
  const { projectId } = Route.useParams()
  useProjectLoader(projectId)
  const canvasViewportRef = useRef<GraphCanvasViewportRef | null>(null)
  const [selectedNodeIds, setSelectedNodeIds] = useState<string[]>([])
  const nodes = useGraphStore((s) => s.nodes)
  const addNode = useGraphStore((s) => s.addNode)
  const removeNode = useGraphStore((s) => s.removeNode)

  const handleAddNode = useCallback(
    (type: 'computation' | 'presentation') => {
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
    (params: { nodes: { id: string }[] }) => {
      setSelectedNodeIds(params.nodes.map((n) => n.id))
    },
    [],
  )

  useEffect(() => {
    const onKeyDown = (e: KeyboardEvent) => {
      if (selectedNodeIds.length === 0) return
      if (e.key === 'Delete' || e.key === 'Backspace') {
        e.preventDefault()
        handleDeleteSelected()
      }
    }
    window.addEventListener('keydown', onKeyDown)
    return () => window.removeEventListener('keydown', onKeyDown)
  }, [selectedNodeIds.length, handleDeleteSelected])

  return (
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
          onSelectionChange={handleSelectionChange}
        />
      </div>
    </div>
  )
}
