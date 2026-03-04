/**
 * Export (download JSON) and Import (file → new project) for projects.
 */

import { getFileBlob, putFileBlob } from '~/lib/file-blob-idb'
import { setProjectSnapshot } from '~/lib/project-storage'
import { useProjectsIndexStore } from '~/store'
import type { ProjectSnapshot } from '~/types/project'
import type { ProjectNode } from '~/types/project'
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
    reader.onload = async () => {
      try {
        const data = JSON.parse(reader.result as string) as unknown
        const snapshot = parseProjectSnapshot(data)
        if (!snapshot) {
          resolve({ error: 'Invalid project file format' })
          return
        }
        const newId = crypto.randomUUID()
        let nodes: ProjectNode[]
        try {
          nodes = await Promise.all(
            snapshot.nodes.map(async (node: ProjectNode): Promise<ProjectNode> => {
              if (node.type !== 'file' || !node.url?.startsWith('indexeddb://')) return node
              const parts = node.url.split('/')
              if (parts.length < 4) return node
              const oldProjectId = parts[2]
              const nodeId = node.id
              const blob = await getFileBlob(oldProjectId, nodeId)
              if (!blob) return node
              await putFileBlob(newId, nodeId, blob)
              return { ...node, url: `indexeddb://${newId}/${nodeId}` }
            }),
          )
        } catch {
          resolve({ error: 'Failed to copy file data from storage.' })
          return
        }
        const newSnapshot: ProjectSnapshot = {
          id: newId,
          version: snapshot.version,
          nodes,
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
