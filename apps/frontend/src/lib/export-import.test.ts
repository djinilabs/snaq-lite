import { describe, it, expect, vi, beforeEach } from 'vitest'
import { buildDownloadBlob, importProjectFile } from './export-import'
import { getProjectSnapshot, PROJECTS_INDEX_KEY, PROJECT_KEY_PREFIX } from './project-storage'
import { useProjectsIndexStore } from '~/store'

describe('export-import', () => {
  beforeEach(() => {
    localStorage.removeItem(PROJECTS_INDEX_KEY)
    const keys: string[] = []
    for (let i = 0; i < localStorage.length; i++) {
      const key = localStorage.key(i)
      if (key?.startsWith(PROJECT_KEY_PREFIX)) keys.push(key)
    }
    keys.forEach((k) => localStorage.removeItem(k))
    useProjectsIndexStore.setState({ projects: [], hydrated: true })
  })

  describe('buildDownloadBlob', () => {
    it('returns blob with application/json type and correct filename', () => {
      const snapshot = {
        id: 'export-id-123',
        version: 1,
        nodes: [{ id: 'n1', position: { x: 0, y: 0 }, type: 'computation' as const }],
        edges: [],
      }
      const { blob, filename } = buildDownloadBlob(snapshot)
      expect(blob.type).toBe('application/json')
      expect(filename).toBe('project-export-id-123.snaq.json')
      expect(blob.size).toBeGreaterThan(0)
      const expectedJson = JSON.stringify(snapshot, null, 2)
      expect(blob.size).toBe(expectedJson.length)
    })

    it('builds blob from pretty-printed JSON', () => {
      const snapshot = { id: 's1', nodes: [], edges: [] }
      const { blob } = buildDownloadBlob(snapshot)
      const expectedJson = JSON.stringify(snapshot, null, 2)
      expect(blob.size).toBe(expectedJson.length)
      expect(expectedJson).toContain('\n')
    })
  })

  describe('importProjectFile', () => {
    it('creates new project with new UUID and persists snapshot and index', async () => {
      const file = new File(
        [
          JSON.stringify({
            id: 'old-id',
            version: 1,
            nodes: [{ id: 'n1', position: { x: 0, y: 0 }, type: 'computation', content: '1' }],
            edges: [],
          }),
        ],
        'imported.snaq.json',
        { type: 'application/json' },
      )
      const result = await importProjectFile(file)
      expect('error' in result).toBe(false)
      expect((result as { id: string }).id).toBeDefined()
      const id = (result as { id: string }).id
      expect(id).not.toBe('old-id')
      const stored = getProjectSnapshot(id)
      expect(stored).not.toBeNull()
      expect(stored?.nodes).toHaveLength(1)
      expect(stored?.nodes[0].content).toBe('1')
      expect(stored?.id).toBe(id)
      expect(useProjectsIndexStore.getState().projects.some((p) => p.id === id)).toBe(true)
    })

    it('returns error for invalid JSON', async () => {
      const file = new File(['not json'], 'x.json', { type: 'application/json' })
      const result = await importProjectFile(file)
      expect(result).toEqual({ error: 'Invalid JSON' })
    })

    it('returns error for invalid project file format', async () => {
      const file = new File([JSON.stringify({ id: 'x' })], 'x.json', { type: 'application/json' })
      const result = await importProjectFile(file)
      expect(result).toEqual({ error: 'Invalid project file format' })
    })

    it('returns error when file read fails', async () => {
      const file = new File(['valid'], 'x.json', { type: 'application/json' })
      const readAsText = vi.spyOn(FileReader.prototype, 'readAsText').mockImplementation(function (this: FileReader) {
        queueMicrotask(() => {
          if (this.onerror) this.onerror(new ProgressEvent('error'))
        })
      })
      const result = await importProjectFile(file)
      expect(result).toEqual({ error: 'Failed to read file' })
      readAsText.mockRestore()
    })
  })
})
