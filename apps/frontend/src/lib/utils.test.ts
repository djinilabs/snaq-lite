import { describe, it, expect } from 'vitest'
import { generateWidgetId } from './utils'

describe('lib/utils', () => {
  describe('generateWidgetId', () => {
    it('returns a string', () => {
      expect(typeof generateWidgetId()).toBe('string')
    })
    it('starts with w-', () => {
      expect(generateWidgetId()).toMatch(/^w-/)
    })
    it('returns unique values on multiple calls', () => {
      const a = generateWidgetId()
      const b = generateWidgetId()
      expect(a).not.toBe(b)
    })
  })
})
