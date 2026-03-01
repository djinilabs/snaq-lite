/**
 * Toolbar for the canvas page: Back to projects, Save, Export, Add blocks, Rename, Delete project.
 */

import { Link, useNavigate } from '@tanstack/react-router'
import { downloadProjectSnapshot } from '~/lib/export-import'
import { buildSnapshotFromGraph, setProjectSnapshot } from '~/lib/project-storage'
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

  const saveCurrent = () => {
    const snapshot = getCurrentSnapshot(projectId)
    setProjectSnapshot(snapshot)
    const projectsState = useProjectsIndexStore.getState().projects
    const updated = projectsState.map((p) =>
      p.id === projectId ? { ...p, updatedAt: Date.now() } : p,
    )
    useProjectsIndexStore.getState().setProjects(updated)
  }

  const handleExport = () => {
    downloadProjectSnapshot(getCurrentSnapshot(projectId))
  }

  return (
    <div
      data-testid="canvas-toolbar"
      style={{
        display: 'flex',
        alignItems: 'center',
        gap: 12,
        padding: '8px 12px',
        background: '#1e1e2e',
        borderBottom: '1px solid #333',
      }}
    >
      <Link to="/" data-testid="back-to-projects" style={{ color: '#8ab4f8', textDecoration: 'none' }}>
        Back to projects
      </Link>
      <button
        type="button"
        data-testid="save-btn"
        onClick={saveCurrent}
        style={{
          padding: '4px 10px',
          cursor: 'pointer',
          background: '#333',
          color: '#fff',
          border: '1px solid #555',
          borderRadius: 4,
        }}
      >
        Save
      </button>
      <button
        type="button"
        data-testid="export-btn"
        onClick={handleExport}
        style={{
          padding: '4px 10px',
          cursor: 'pointer',
          background: '#333',
          color: '#fff',
          border: '1px solid #555',
          borderRadius: 4,
        }}
      >
        Export
      </button>
      <span style={{ width: 1, height: 16, background: '#555', marginLeft: 4 }} />
      <button
        type="button"
        data-testid="add-computation-btn"
        onClick={() => onAddNode?.('computation')}
        style={{
          padding: '4px 10px',
          cursor: 'pointer',
          background: '#333',
          color: '#fff',
          border: '1px solid #555',
          borderRadius: 4,
        }}
      >
        Add computation box
      </button>
      <button
        type="button"
        data-testid="add-presentation-btn"
        onClick={() => onAddNode?.('presentation')}
        style={{
          padding: '4px 10px',
          cursor: 'pointer',
          background: '#333',
          color: '#fff',
          border: '1px solid #555',
          borderRadius: 4,
        }}
      >
        Add presentation block
      </button>
      {onDeleteSelected && (
        <button
          type="button"
          data-testid="delete-selected-btn"
          onClick={onDeleteSelected}
          disabled={!hasSelection}
          style={{
            padding: '4px 10px',
            cursor: hasSelection ? 'pointer' : 'not-allowed',
            background: '#333',
            color: hasSelection ? '#f87171' : '#666',
            border: '1px solid #555',
            borderRadius: 4,
          }}
        >
          Delete selected
        </button>
      )}
      <span style={{ width: 1, height: 16, background: '#555', marginLeft: 4 }} />
      <button
        type="button"
        data-testid="rename-btn"
        onClick={() => {
          const name = window.prompt('Project name', meta?.name ?? '')
          if (name != null) updateProjectName(projectId, name)
        }}
        style={{
          padding: '4px 10px',
          cursor: 'pointer',
          background: '#333',
          color: '#fff',
          border: '1px solid #555',
          borderRadius: 4,
        }}
      >
        Rename
      </button>
      <button
        type="button"
        data-testid="delete-project-btn"
        onClick={() => {
          if (window.confirm('Delete this project? This cannot be undone.')) {
            removeProject(projectId)
            navigate({ to: '/' })
          }
        }}
        style={{
          padding: '4px 10px',
          cursor: 'pointer',
          background: '#444',
          color: '#f87171',
          border: '1px solid #555',
          borderRadius: 4,
        }}
      >
        Delete project
      </button>
    </div>
  )
}
