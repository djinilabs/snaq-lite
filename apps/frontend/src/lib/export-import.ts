/**
 * Export (download JSON) and Import (file → new project) for projects.
 */

import { setProjectSnapshot } from '~/lib/project-storage'
import { useProjectsIndexStore } from '~/store'
import type { ProjectSnapshot } from '~/types/project'
import { parseProjectSnapshot } from '~/types/project'

/** Build blob and filename for a snapshot (testable without DOM/URL). */
export function buildDownloadBlob(snapshot: ProjectSnapshot): { blob: Blob; filename: string } {
  const blob = new Blob([JSON.stringify(snapshot, null, 2)], {
    type: 'application/json',
  })
  return { blob, filename: `project-${snapshot.id}.snaq.json` }
}

export function downloadProjectSnapshot(snapshot: ProjectSnapshot): void {
  const { blob, filename } = buildDownloadBlob(snapshot)
  const url = URL.createObjectURL(blob)
  const a = document.createElement('a')
  a.href = url
  a.download = filename
  a.click()
  URL.revokeObjectURL(url)
}

export function importProjectFile(file: File): Promise<{ id: string } | { error: string }> {
  return new Promise((resolve) => {
    const reader = new FileReader()
    reader.onload = () => {
      try {
        const data = JSON.parse(reader.result as string) as unknown
        const snapshot = parseProjectSnapshot(data)
        if (!snapshot) {
          resolve({ error: 'Invalid project file format' })
          return
        }
        const newId = crypto.randomUUID()
        const newSnapshot: ProjectSnapshot = {
          id: newId,
          version: snapshot.version,
          nodes: snapshot.nodes,
          edges: snapshot.edges,
        }
        setProjectSnapshot(newSnapshot)
        useProjectsIndexStore.getState().addProject({
          id: newId,
          name: undefined,
          updatedAt: Date.now(),
        })
        resolve({ id: newId })
      } catch {
        resolve({ error: 'Invalid JSON' })
      }
    }
    reader.onerror = () => resolve({ error: 'Failed to read file' })
    reader.readAsText(file)
  })
}
