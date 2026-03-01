import { useMemo, useRef } from 'react'
import { createFileRoute, useNavigate } from '@tanstack/react-router'
import { importProjectFile } from '~/lib/export-import'
import { setProjectSnapshot } from '~/lib/project-storage'
import { sortProjectsByUpdatedAt } from '~/lib/project-list-sort'
import { useProjectsIndexStore, useUIStore } from '~/store'

export const Route = createFileRoute('/')({
  component: ProjectListPage,
})

function ProjectListPage() {
  const navigate = useNavigate()
  const projects = useProjectsIndexStore((s) => s.projects)
  const sortedProjects = useMemo(() => sortProjectsByUpdatedAt(projects), [projects])
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
      data-testid="project-list-page"
      style={{
        minHeight: '100vh',
        background: 'var(--bg-primary)',
        color: 'var(--text-primary)',
        padding: 32,
        maxWidth: 640,
        margin: '0 auto',
      }}
    >
      <h1 style={{ margin: '0 0 8px', fontSize: 28, fontWeight: 600 }}>Projects</h1>
      <p style={{ margin: '0 0 24px', color: 'var(--text-secondary)', fontSize: 15 }}>
        Create a project or import a file to get started.
      </p>
      <div style={{ display: 'flex', gap: 12, marginBottom: 32 }}>
        <button
          type="button"
          data-testid="new-project-btn"
          onClick={handleNewProject}
          style={{
            padding: '10px 20px',
            cursor: 'pointer',
            background: 'var(--accent)',
            color: '#fff',
            border: 'none',
            borderRadius: 'var(--radius-sm)',
            fontWeight: 500,
          }}
        >
          New project
        </button>
        <button
          type="button"
          data-testid="import-btn"
          onClick={handleImport}
          style={{
            padding: '10px 20px',
            cursor: 'pointer',
            background: 'var(--bg-elevated)',
            color: 'var(--text-primary)',
            border: '1px solid var(--border)',
            borderRadius: 'var(--radius-sm)',
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
          data-testid="import-file-input"
        />
      </div>
      {sortedProjects.length === 0 ? (
        <p style={{ color: 'var(--text-muted)' }}>No projects yet. Create one or import a file.</p>
      ) : (
        <ul data-testid="project-list" style={{ listStyle: 'none', padding: 0, margin: 0 }}>
          {sortedProjects.map((p) => (
            <li
              key={p.id}
              data-testid="project-item"
              data-project-id={p.id}
              style={{
                display: 'flex',
                alignItems: 'center',
                justifyContent: 'space-between',
                padding: '16px 20px',
                marginBottom: 10,
                background: 'var(--bg-card)',
                borderRadius: 'var(--radius)',
                border: '1px solid var(--border)',
                boxShadow: 'var(--shadow-sm)',
              }}
            >
              <span style={{ fontWeight: 500 }}>
                {p.name ?? 'Untitled'}{' '}
                <span style={{ color: 'var(--text-muted)', fontSize: 13, fontWeight: 400 }}>
                  ({p.id.slice(0, 8)}…)
                </span>
              </span>
              <div style={{ display: 'flex', gap: 8 }}>
                <button
                  type="button"
                  onClick={() => handleOpen(p.id)}
                  style={{
                    padding: '6px 14px',
                    cursor: 'pointer',
                    background: 'var(--accent)',
                    color: '#fff',
                    border: 'none',
                    borderRadius: 'var(--radius-sm)',
                    fontWeight: 500,
                  }}
                >
                  Open
                </button>
                <button
                  type="button"
                  onClick={() => handleDelete(p.id)}
                  style={{
                    padding: '6px 14px',
                    cursor: 'pointer',
                    background: 'transparent',
                    color: 'var(--danger)',
                    border: '1px solid var(--border)',
                    borderRadius: 'var(--radius-sm)',
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
