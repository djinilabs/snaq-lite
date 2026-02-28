import { describe, it, expect } from 'vitest'
import {
  computationNodeMinHeight,
  computationNodeHandleTop,
} from './computation-box-layout'

describe('computation-box-layout', () => {
  describe('computationNodeMinHeight', () => {
    it('returns base min height when input count is 0', () => {
      expect(computationNodeMinHeight(0)).toBe(120)
    })

    it('returns base min height for 1 input when formula is below base', () => {
      // 32 + 1*24 + 16 = 72 < 120
      expect(computationNodeMinHeight(1)).toBe(120)
    })

    it('returns formula height when input count makes it exceed base', () => {
      // 32 + 3*24 + 16 = 120
      expect(computationNodeMinHeight(3)).toBe(120)
      // 32 + 4*24 + 16 = 144
      expect(computationNodeMinHeight(4)).toBe(144)
      expect(computationNodeMinHeight(5)).toBe(168)
    })
  })

  describe('computationNodeHandleTop', () => {
    it('returns 32 for first handle (index 0)', () => {
      expect(computationNodeHandleTop(0)).toBe(32)
    })

    it('returns 32 + 24*i for successive handles', () => {
      expect(computationNodeHandleTop(1)).toBe(56)
      expect(computationNodeHandleTop(2)).toBe(80)
      expect(computationNodeHandleTop(3)).toBe(104)
    })

    it('clamps negative index to 0', () => {
      expect(computationNodeHandleTop(-1)).toBe(32)
    })
  })

  describe('computationNodeMinHeight (edge cases)', () => {
    it('clamps negative input count to 0', () => {
      expect(computationNodeMinHeight(-1)).toBe(120)
    })
  })
})
