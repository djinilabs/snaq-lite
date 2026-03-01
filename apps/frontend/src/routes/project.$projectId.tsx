import { useState, useCallback, useEffect } from 'react'
import { createFileRoute } from '@tanstack/react-router'
import { GraphCanvas } from '~/components/canvas/graph-canvas'
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
  const [selectedNodeIds, setSelectedNodeIds] = useState<string[]>([])
  const nodes = useGraphStore((s) => s.nodes)
  const addNode = useGraphStore((s) => s.addNode)
  const removeNode = useGraphStore((s) => s.removeNode)

  const handleAddNode = useCallback(
    (type: 'computation' | 'presentation') => {
      const id = crypto.randomUUID()
      const position = { x: 150 + nodes.length * 30, y: 100 + nodes.length * 40 }
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
    <div data-testid="canvas-page" style={{ display: 'flex', flexDirection: 'column', width: '100vw', height: '100vh' }}>
      <ProjectToolbar
        projectId={projectId}
        onAddNode={handleAddNode}
        onDeleteSelected={handleDeleteSelected}
        hasSelection={selectedNodeIds.length > 0}
      />
      <div data-testid="graph-canvas-wrapper" style={{ flex: 1, minHeight: 0 }}>
        <GraphCanvas
          selectedNodeIds={selectedNodeIds}
          onSelectionChange={(params) => setSelectedNodeIds(params.nodes.map((n) => n.id))}
        />
      </div>
    </div>
  )
}
