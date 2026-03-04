import { describe, it, expect, beforeEach, vi } from 'vitest'
import {
  setProjectSnapshot,
  getProjectSnapshot,
  PROJECTS_INDEX_KEY,
} from '~/lib/project-storage'
import { useProjectsIndexStore } from './projects-index-store'

vi.mock('~/lib/file-blob-idb', () => ({
  deleteAllBlobsForProject: vi.fn().mockResolvedValue(undefined),
}))

describe('projects-index-store', () => {
  beforeEach(() => {
    localStorage.removeItem(PROJECTS_INDEX_KEY)
    useProjectsIndexStore.setState({ projects: [], hydrated: false })
  })

  it('hydrate loads from localStorage', () => {
    localStorage.setItem(
      PROJECTS_INDEX_KEY,
      JSON.stringify([{ id: 'p1', name: 'First', updatedAt: 100 }]),
    )
    useProjectsIndexStore.getState().hydrate()
    expect(useProjectsIndexStore.getState().projects).toEqual([
      { id: 'p1', name: 'First', updatedAt: 100 },
    ])
    expect(useProjectsIndexStore.getState().hydrated).toBe(true)
  })

  it('addProject appends and persists', () => {
    useProjectsIndexStore.getState().hydrate()
    useProjectsIndexStore.getState().addProject({ id: 'new', updatedAt: 200 })
    expect(useProjectsIndexStore.getState().projects).toHaveLength(1)
    expect(useProjectsIndexStore.getState().projects[0]).toMatchObject({
      id: 'new',
      updatedAt: 200,
    })
    expect(JSON.parse(localStorage.getItem(PROJECTS_INDEX_KEY) ?? '[]')).toHaveLength(1)
  })

  it('removeProject removes and persists', () => {
    localStorage.setItem(
      PROJECTS_INDEX_KEY,
      JSON.stringify([{ id: 'a' }, { id: 'b' }]),
    )
    useProjectsIndexStore.getState().hydrate()
    useProjectsIndexStore.getState().removeProject('a')
    expect(useProjectsIndexStore.getState().projects).toHaveLength(1)
    expect(useProjectsIndexStore.getState().projects[0].id).toBe('b')
  })

  it('updateProjectName updates and persists', () => {
    localStorage.setItem(PROJECTS_INDEX_KEY, JSON.stringify([{ id: 'p1' }]))
    useProjectsIndexStore.getState().hydrate()
    useProjectsIndexStore.getState().updateProjectName('p1', 'Renamed')
    expect(useProjectsIndexStore.getState().projects[0].name).toBe('Renamed')
  })

  it('removeProject deletes project snapshot from localStorage', () => {
    const id = 'to-remove'
    setProjectSnapshot({ id, nodes: [], edges: [] })
    localStorage.setItem(PROJECTS_INDEX_KEY, JSON.stringify([{ id }]))
    useProjectsIndexStore.getState().hydrate()
    useProjectsIndexStore.getState().removeProject(id)
    expect(getProjectSnapshot(id)).toBeNull()
  })
})
