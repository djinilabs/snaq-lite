/**
 * Toolbar for the canvas page: Back to projects, Export, Undo, Redo, Add blocks, Rename, Delete project.
 */

import { Link, useNavigate } from '@tanstack/react-router'
import { downloadProjectSnapshot } from '~/lib/export-import'
import { buildSnapshotFromGraph } from '~/lib/project-storage'
import { performRedo, performUndo } from '~/lib/perform-undo-redo'
import { useGraphStore } from '~/store'
import { useProjectsIndexStore } from '~/store'

export interface ProjectToolbarProps {
  projectId: string
  onAddNode?: (type: 'computation' | 'presentation') => void
  onDeleteSelected?: () => void
  hasSelection?: boolean
}

function getCurrentSnapshot(projectId: string) {
  const nodes = useGraphStore.getState().nodes
  const edges = useGraphStore.getState().edges
  return buildSnapshotFromGraph(projectId, nodes, edges)
}

export function ProjectToolbar({ projectId, onAddNode, onDeleteSelected, hasSelection }: ProjectToolbarProps) {
  const navigate = useNavigate()
  const projects = useProjectsIndexStore((s) => s.projects)
  const meta = projects.find((p) => p.id === projectId)
  const updateProjectName = useProjectsIndexStore((s) => s.updateProjectName)
  const removeProject = useProjectsIndexStore((s) => s.removeProject)
  const undoStackLength = useGraphStore((s) => s.undoStack.length)
  const redoStackLength = useGraphStore((s) => s.redoStack.length)

  const handleUndo = () => {
    performUndo()
  }

  const handleRedo = () => {
    performRedo()
  }

  const handleExport = () => {
    downloadProjectSnapshot(getCurrentSnapshot(projectId))
  }

  return (
    <div
      className="canvas-toolbar"
      data-testid="canvas-toolbar"
      style={{
        display: 'flex',
        alignItems: 'center',
        gap: 10,
        padding: '10px 16px',
        background: 'var(--bg-secondary)',
        borderBottom: '1px solid var(--border)',
      }}
    >
      <Link
        to="/"
        data-testid="back-to-projects"
        style={{ color: 'var(--accent)', textDecoration: 'none', fontWeight: 500 }}
      >
        ← Back to projects
      </Link>
      <span style={{ width: 1, height: 18, background: 'var(--border)', margin: '0 4px' }} />
      <button
        type="button"
        data-testid="undo-btn"
        onClick={handleUndo}
        disabled={undoStackLength === 0}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)' }}
      >
        Undo
      </button>
      <button
        type="button"
        data-testid="redo-btn"
        onClick={handleRedo}
        disabled={redoStackLength === 0}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)' }}
      >
        Redo
      </button>
      <button
        type="button"
        data-testid="export-btn"
        onClick={handleExport}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)' }}
      >
        Export
      </button>
      <span style={{ width: 1, height: 18, background: 'var(--border)', margin: '0 4px' }} />
      <button
        type="button"
        data-testid="add-computation-btn"
        data-accent
        onClick={() => onAddNode?.('computation')}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)', fontWeight: 500 }}
      >
        Add computation box
      </button>
      <button
        type="button"
        data-testid="add-presentation-btn"
        onClick={() => onAddNode?.('presentation')}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)' }}
      >
        Add presentation block
      </button>
      {onDeleteSelected && (
        <button
          type="button"
          data-testid="delete-selected-btn"
          data-danger-soft={hasSelection ? '' : undefined}
          onClick={onDeleteSelected}
          disabled={!hasSelection}
          style={{ padding: '6px 12px', borderRadius: 'var(--radius-sm)' }}
        >
          Delete selected
        </button>
      )}
      <span style={{ flex: 1 }} />
      <button
        type="button"
        data-testid="rename-btn"
        onClick={() => {
          const name = window.prompt('Project name', meta?.name ?? '')
          if (name != null) updateProjectName(projectId, name)
        }}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)' }}
      >
        Rename
      </button>
      <button
        type="button"
        data-testid="delete-project-btn"
        data-danger-outline
        onClick={() => {
          if (window.confirm('Delete this project? This cannot be undone.')) {
            removeProject(projectId)
            navigate({ to: '/' })
          }
        }}
        style={{ padding: '6px 12px', cursor: 'pointer', borderRadius: 'var(--radius-sm)' }}
      >
        Delete project
      </button>
    </div>
  )
}
