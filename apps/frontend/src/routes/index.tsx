import { useMemo, useRef } from 'react'
import { createFileRoute, useNavigate } from '@tanstack/react-router'
import { importProjectFile } from '~/lib/export-import'
import { setProjectSnapshot } from '~/lib/project-storage'
import { useProjectsIndexStore, useUIStore } from '~/store'

export const Route = createFileRoute('/')({
  component: ProjectListPage,
})

function ProjectListPage() {
  const navigate = useNavigate()
  const projects = useProjectsIndexStore((s) => s.projects)
  const sortedProjects = useMemo(
    () => [...projects].sort((a, b) => (b.updatedAt ?? 0) - (a.updatedAt ?? 0)),
    [projects],
  )
  const addProject = useProjectsIndexStore((s) => s.addProject)
  const removeProject = useProjectsIndexStore((s) => s.removeProject)
  const fileInputRef = useRef<HTMLInputElement>(null)

  const handleNewProject = () => {
    const id = crypto.randomUUID()
    setProjectSnapshot({ id, version: 1, nodes: [], edges: [] })
    addProject({ id, updatedAt: Date.now() })
    navigate({ to: '/project/$projectId', params: { projectId: id } })
  }

  const handleImport = () => {
    fileInputRef.current?.click()
  }

  const onFileChange = async (e: React.ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0]
    e.target.value = ''
    if (!file) return
    const result = await importProjectFile(file)
    if ('error' in result) {
      useUIStore.getState().addToast(result.error, 'error')
      return
    }
    navigate({ to: '/project/$projectId', params: { projectId: result.id } })
  }

  const handleOpen = (id: string) => {
    navigate({ to: '/project/$projectId', params: { projectId: id } })
  }

  const handleDelete = (id: string) => {
    if (window.confirm('Delete this project? This cannot be undone.')) {
      removeProject(id)
    }
  }

  return (
    <div
      style={{
        minHeight: '100vh',
        background: '#1e1e2e',
        color: '#e4e4e7',
        padding: 24,
      }}
    >
      <h1 style={{ marginBottom: 24 }}>Projects</h1>
      <div style={{ display: 'flex', gap: 12, marginBottom: 24 }}>
        <button
          type="button"
          onClick={handleNewProject}
          style={{
            padding: '8px 16px',
            cursor: 'pointer',
            background: '#3b82f6',
            color: '#fff',
            border: 'none',
            borderRadius: 6,
          }}
        >
          New project
        </button>
        <button
          type="button"
          onClick={handleImport}
          style={{
            padding: '8px 16px',
            cursor: 'pointer',
            background: '#333',
            color: '#fff',
            border: '1px solid #555',
            borderRadius: 6,
          }}
        >
          Import
        </button>
        <input
          ref={fileInputRef}
          type="file"
          accept=".json,.snaq.json"
          style={{ display: 'none' }}
          onChange={onFileChange}
        />
      </div>
      {sortedProjects.length === 0 ? (
        <p style={{ color: '#888' }}>No projects yet. Create one or import a file.</p>
      ) : (
        <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
          {sortedProjects.map((p) => (
            <li
              key={p.id}
              style={{
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'space-between',
                padding: '12px 16px',
                marginBottom: 8,
                background: '#2d2d44',
                borderRadius: 8,
                border: '1px solid #444',
              }}
            >
              <span>
                {p.name ?? 'Untitled'} <span style={{ color: '#666', fontSize: 12 }}>({p.id.slice(0, 8)}…)</span>
              </span>
              <div style={{ display: 'flex', gap: 8 }}>
                <button
                  type="button"
                  onClick={() => handleOpen(p.id)}
                  style={{
                    padding: '4px 12px',
                    cursor: 'pointer',
                    background: '#333',
                    color: '#fff',
                    border: '1px solid #555',
                    borderRadius: 4,
                  }}
                >
                  Open
                </button>
                <button
                  type="button"
                  onClick={() => handleDelete(p.id)}
                  style={{
                    padding: '4px 12px',
                    cursor: 'pointer',
                    background: '#444',
                    color: '#f87171',
                    border: '1px solid #555',
                    borderRadius: 4,
                  }}
                >
                  Delete
                </button>
              </div>
            </li>
          ))}
        </ul>
      )}
    </div>
  )
}
