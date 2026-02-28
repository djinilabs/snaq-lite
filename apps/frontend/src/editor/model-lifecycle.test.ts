import { describe, it, expect } from 'vitest'
import { getRemovedNodeIds } from './model-lifecycle'

describe('model-lifecycle', () => {
  describe('getRemovedNodeIds', () => {
    it('returns ids that were in prev but not in current nodes', () => {
      const prev = new Set(['a', 'b', 'c'])
      const nodes = [{ id: 'a' }, { id: 'c' }]
      expect(getRemovedNodeIds(prev, nodes)).toEqual(['b'])
    })

    it('returns empty when all prev ids still in nodes', () => {
      const prev = new Set(['a', 'b'])
      const nodes = [{ id: 'a' }, { id: 'b' }]
      expect(getRemovedNodeIds(prev, nodes)).toEqual([])
    })

    it('returns all prev ids when nodes is empty', () => {
      const prev = new Set(['a', 'b'])
      expect(getRemovedNodeIds(prev, [])).toEqual(['a', 'b'])
    })

    it('returns empty when prev is empty', () => {
      expect(getRemovedNodeIds(new Set(), [{ id: 'x' }])).toEqual([])
    })

    it('returns multiple removed ids', () => {
      const prev = new Set(['n1', 'n2', 'n3', 'n4'])
      const nodes = [{ id: 'n2' }]
      const removed = getRemovedNodeIds(prev, nodes)
      expect(removed).toHaveLength(3)
      expect(removed).toContain('n1')
      expect(removed).toContain('n3')
      expect(removed).toContain('n4')
    })
  })
})
