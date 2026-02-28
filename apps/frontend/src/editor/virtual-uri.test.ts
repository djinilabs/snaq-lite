import { describe, it, expect } from 'vitest'
import { nodeIdToUri, uriToNodeId, isGraphNodeUri } from './virtual-uri'

describe('virtual-uri', () => {
  describe('nodeIdToUri', () => {
    it('returns snaq://graph/<id>.sl for given node id', () => {
      expect(nodeIdToUri('node_42')).toBe('snaq://graph/node_42.sl')
      expect(nodeIdToUri('a')).toBe('snaq://graph/a.sl')
    })
  })

  describe('uriToNodeId', () => {
    it('extracts node id from valid graph URI', () => {
      expect(uriToNodeId('snaq://graph/node_42.sl')).toBe('node_42')
      expect(uriToNodeId('snaq://graph/a.sl')).toBe('a')
    })
    it('returns null for non-graph URI', () => {
      expect(uriToNodeId('file:///foo.sl')).toBeNull()
      expect(uriToNodeId('snaq://graph/')).toBeNull()
    })
    it('returns null when URI does not end with .sl', () => {
      expect(uriToNodeId('snaq://graph/node_42.txt')).toBeNull()
    })
    it('returns null when URI does not start with prefix', () => {
      expect(uriToNodeId('other://graph/node_42.sl')).toBeNull()
    })
  })

  describe('isGraphNodeUri', () => {
    it('returns true for snaq://graph/ URIs', () => {
      expect(isGraphNodeUri('snaq://graph/node_42.sl')).toBe(true)
      expect(isGraphNodeUri('snaq://graph/anything.sl')).toBe(true)
    })
    it('returns false for other schemes', () => {
      expect(isGraphNodeUri('file:///x.sl')).toBe(false)
      expect(isGraphNodeUri('inmemory://model/snaq/graph/node_42.sl')).toBe(false)
    })
  })
})
