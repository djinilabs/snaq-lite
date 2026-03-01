import { describe, it, expect } from 'vitest'
import { sortProjectsByUpdatedAt } from './project-list-sort'

describe('sortProjectsByUpdatedAt', () => {
  it('sorts by updatedAt descending', () => {
    const projects = [
      { id: 'a', updatedAt: 100 },
      { id: 'b', updatedAt: 300 },
      { id: 'c', updatedAt: 200 },
    ]
    expect(sortProjectsByUpdatedAt(projects).map((p) => p.id)).toEqual(['b', 'c', 'a'])
  })

  it('treats missing updatedAt as 0', () => {
    const projects = [
      { id: 'a', updatedAt: 10 },
      { id: 'b' },
      { id: 'c', updatedAt: 5 },
    ]
    expect(sortProjectsByUpdatedAt(projects).map((p) => p.id)).toEqual(['a', 'c', 'b'])
  })

  it('does not mutate original array', () => {
    const projects = [{ id: 'a', updatedAt: 1 }, { id: 'b', updatedAt: 2 }]
    sortProjectsByUpdatedAt(projects)
    expect(projects.map((p) => p.id)).toEqual(['a', 'b'])
  })

  it('returns empty array for empty input', () => {
    expect(sortProjectsByUpdatedAt([])).toEqual([])
  })

  it('preserves other properties of each item', () => {
    const projects = [
      { id: 'a', name: 'First', updatedAt: 100 },
      { id: 'b', name: 'Second', updatedAt: 200 },
    ]
    const sorted = sortProjectsByUpdatedAt(projects)
    expect(sorted[0]).toEqual({ id: 'b', name: 'Second', updatedAt: 200 })
    expect(sorted[1]).toEqual({ id: 'a', name: 'First', updatedAt: 100 })
  })
})
