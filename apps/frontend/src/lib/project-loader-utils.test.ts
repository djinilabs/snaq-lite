import { describe, it, expect } from 'vitest'
import {
  isValidUuid,
  snapshotEdgesToGraphEdges,
  snapshotToGraphNodes,
} from './project-loader-utils'
import { VIRTUAL_URI_PREFIX } from './constants'

describe('project-loader-utils', () => {
  describe('isValidUuid', () => {
    it('accepts valid RFC 4122 UUIDs', () => {
      expect(isValidUuid('550e8400-e29b-41d4-a716-446655440000')).toBe(true)
      expect(isValidUuid('6ba7b810-9dad-11d1-80b4-00c04fd430c8')).toBe(true)
      expect(isValidUuid('01234567-89ab-4def-8123-456789abcdef')).toBe(true)
    })

    it('rejects empty or non-string', () => {
      expect(isValidUuid('')).toBe(false)
    })

    it('rejects invalid format', () => {
      expect(isValidUuid('not-a-uuid')).toBe(false)
      expect(isValidUuid('550e8400e29b41d4a716446655440000')).toBe(false)
      expect(isValidUuid('550e8400-e29b-41d4-a716')).toBe(false)
    })

    it('rejects wrong variant (first digit of third group must be 1-5)', () => {
      expect(isValidUuid('550e8400-e29b-61d4-a716-446655440000')).toBe(false)
    })

    it('rejects wrong version (second digit of third group 89ab for version 4)', () => {
      expect(isValidUuid('550e8400-e29b-41d4-c716-446655440000')).toBe(false)
    })
  })

  describe('snapshotToGraphNodes', () => {
    it('maps computation nodes with content to initialContent', () => {
      const snapshot = {
        id: 'p',
        nodes: [
          { id: 'n1', position: { x: 0, y: 0 }, type: 'computation' as const, content: '1 + 1' },
        ],
        edges: [],
      }
      const nodes = snapshotToGraphNodes(snapshot)
      expect(nodes).toHaveLength(1)
      expect(nodes[0].id).toBe('n1')
      expect(nodes[0].position).toEqual({ x: 0, y: 0 })
      expect(nodes[0].type).toBe('computation')
      expect(nodes[0].uri).toBe(`${VIRTUAL_URI_PREFIX}n1.sl`)
      expect(nodes[0].initialContent).toBe('1 + 1')
    })

    it('maps computation nodes without content to empty string initialContent', () => {
      const snapshot = {
        id: 'p',
        nodes: [{ id: 'n1', position: { x: 0, y: 0 }, type: 'computation' as const }],
        edges: [],
      }
      const nodes = snapshotToGraphNodes(snapshot)
      expect(nodes[0].initialContent).toBe('')
    })

    it('maps presentation nodes without initialContent', () => {
      const snapshot = {
        id: 'p',
        nodes: [
          { id: 'n2', position: { x: 100, y: 50 }, type: 'presentation' as const, content: 'ignored' },
        ],
        edges: [],
      }
      const nodes = snapshotToGraphNodes(snapshot)
      expect(nodes[0].type).toBe('presentation')
      expect(nodes[0].uri).toBe(`${VIRTUAL_URI_PREFIX}n2.sl`)
      expect(nodes[0].initialContent).toBeUndefined()
    })

    it('maps file nodes with optional url', () => {
      const snapshot = {
        id: 'p',
        nodes: [
          { id: 'f1', position: { x: 0, y: 0 }, type: 'file' as const },
          { id: 'f2', position: { x: 50, y: 0 }, type: 'file' as const, url: 'https://example.com/d.csv' },
        ],
        edges: [],
      }
      const nodes = snapshotToGraphNodes(snapshot)
      expect(nodes).toHaveLength(2)
      expect(nodes[0]).toMatchObject({ id: 'f1', type: 'file', uri: `${VIRTUAL_URI_PREFIX}f1.sl` })
      expect(nodes[0].url).toBeUndefined()
      expect(nodes[1]).toMatchObject({ id: 'f2', type: 'file', url: 'https://example.com/d.csv' })
    })

    it('maps multiple nodes and preserves order', () => {
      const snapshot = {
        id: 'p',
        nodes: [
          { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const },
          { id: 'b', position: { x: 1, y: 1 }, type: 'presentation' as const },
        ],
        edges: [],
      }
      const nodes = snapshotToGraphNodes(snapshot)
      expect(nodes.map((n) => n.id)).toEqual(['a', 'b'])
    })

    it('maps computation nodes with inputs to graph inputs', () => {
      const snapshot = {
        id: 'p',
        nodes: [
          {
            id: 'n1',
            position: { x: 0, y: 0 },
            type: 'computation' as const,
            content: '1 + 1',
            inputs: [{ name: 'x', type: 'Vector' }],
          },
        ],
        edges: [],
      }
      const nodes = snapshotToGraphNodes(snapshot)
      expect(nodes[0].inputs).toEqual([{ name: 'x', type: 'Vector' }])
    })
  })

  describe('snapshotEdgesToGraphEdges', () => {
    it('uses targetInputIndex when present and defaults sourceHandle to output', () => {
      const nodes = [
        { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/a.sl' },
        { id: 'b', position: { x: 10, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/b.sl', inputs: [{ name: 'x', type: 'Vector' }] },
      ]
      const snapshotEdges = [{ sourceId: 'a', targetId: 'b', targetInputIndex: 0 }]
      const result = snapshotEdgesToGraphEdges(snapshotEdges, nodes)
      expect(result).toEqual([
        { sourceId: 'a', targetId: 'b', targetInputIndex: 0, sourceHandle: 'output' },
      ])
    })

    it('maps sourceHandle from snapshot edge', () => {
      const nodes = [
        { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/a.sl' },
        { id: 'b', position: { x: 10, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/b.sl', inputs: [{ name: 'x', type: 'Vector' }] },
      ]
      const snapshotEdges = [
        { sourceId: 'a', targetId: 'b', targetInputIndex: 0, sourceHandle: 'output-bottom' },
      ]
      const result = snapshotEdgesToGraphEdges(snapshotEdges, nodes)
      expect(result[0].sourceHandle).toBe('output-bottom')
    })

    it('defaults sourceHandle to output when snapshot has invalid or unknown value', () => {
      const nodes = [
        { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/a.sl' },
        { id: 'b', position: { x: 10, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/b.sl', inputs: [{ name: 'x', type: 'Vector' }] },
      ]
      const snapshotEdges = [
        { sourceId: 'a', targetId: 'b', targetInputIndex: 0, sourceHandle: 'invalid-handle' },
      ]
      const result = snapshotEdgesToGraphEdges(snapshotEdges, nodes)
      expect(result[0].sourceHandle).toBe('output')
    })

    it('resolves legacy targetInputName to index from target node inputs', () => {
      const nodes = [
        { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/a.sl' },
        {
          id: 'b',
          position: { x: 10, y: 0 },
          type: 'computation' as const,
          uri: 'snaq://graph/b.sl',
          inputs: [{ name: 'y', type: 'Vector' }, { name: 'x', type: 'Numeric' }],
        },
      ]
      const snapshotEdges = [{ sourceId: 'a', targetId: 'b', targetInputName: 'x' }]
      const result = snapshotEdgesToGraphEdges(snapshotEdges, nodes)
      expect(result).toEqual([
        { sourceId: 'a', targetId: 'b', targetInputIndex: 1, sourceHandle: 'output' },
      ])
    })

    it('falls back to 0 when legacy targetInputName not found', () => {
      const nodes = [
        { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/a.sl' },
        { id: 'b', position: { x: 10, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/b.sl', inputs: [{ name: 'z', type: 'Vector' }] },
      ]
      const snapshotEdges = [{ sourceId: 'a', targetId: 'b', targetInputName: 'missing' }]
      const result = snapshotEdgesToGraphEdges(snapshotEdges, nodes)
      expect(result).toEqual([
        { sourceId: 'a', targetId: 'b', targetInputIndex: 0, sourceHandle: 'output' },
      ])
    })
  })
})
