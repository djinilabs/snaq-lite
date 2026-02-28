import { describe, it, expect } from 'vitest'
import { isRequest, isResponse, isNotification } from './types'

describe('lsp/types', () => {
  describe('isRequest', () => {
    it('returns true for JSON-RPC request with id and method', () => {
      expect(isRequest({ jsonrpc: '2.0', id: 1, method: 'foo' })).toBe(true)
      expect(isRequest({ jsonrpc: '2.0', id: 'x', method: 'bar', params: {} })).toBe(true)
    })
    it('returns false for response with result', () => {
      expect(isRequest({ jsonrpc: '2.0', id: 1, result: {} })).toBe(false)
    })
    it('returns false for response with error', () => {
      expect(isRequest({ jsonrpc: '2.0', id: 1, error: { code: -1, message: 'x' } })).toBe(false)
    })
    it('returns false for notification (no id)', () => {
      expect(isRequest({ jsonrpc: '2.0', method: 'notif' })).toBe(false)
    })
    it('returns false when both method and result present (response wins)', () => {
      expect(isRequest({ jsonrpc: '2.0', id: 1, method: 'foo', result: {} })).toBe(false)
    })
  })

  describe('isResponse', () => {
    it('returns true for response with result', () => {
      expect(isResponse({ jsonrpc: '2.0', id: 1, result: {} })).toBe(true)
    })
    it('returns true for response with error', () => {
      expect(isResponse({ jsonrpc: '2.0', id: 1, error: { code: -1, message: 'x' } })).toBe(true)
    })
    it('returns false for request', () => {
      expect(isResponse({ jsonrpc: '2.0', id: 1, method: 'foo' })).toBe(false)
    })
    it('returns false for notification', () => {
      expect(isResponse({ jsonrpc: '2.0', method: 'notif' })).toBe(false)
    })
  })

  describe('isNotification', () => {
    it('returns true for notification (method, no id)', () => {
      expect(isNotification({ jsonrpc: '2.0', method: 'snaqlite/graph/nodeSignatureUpdated' })).toBe(true)
    })
    it('returns false for request', () => {
      expect(isNotification({ jsonrpc: '2.0', id: 1, method: 'foo' })).toBe(false)
    })
    it('returns false for response', () => {
      expect(isNotification({ jsonrpc: '2.0', id: 1, result: {} })).toBe(false)
    })
  })
})
