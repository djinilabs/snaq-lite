import { describe, it, expect, beforeEach } from 'vitest'
import {
  getProjectsIndex,
  setProjectsIndex,
  getProjectSnapshot,
  setProjectSnapshot,
  deleteProjectSnapshot,
  buildSnapshotFromGraph,
  getGraphStateForUndo,
  syncModelsToGraphNodes,
  PROJECTS_INDEX_KEY,
  PROJECT_KEY_PREFIX,
} from './project-storage'

describe('project-storage', () => {
  beforeEach(() => {
    localStorage.removeItem(PROJECTS_INDEX_KEY)
    const keys: string[] = []
    for (let i = 0; i < localStorage.length; i++) {
      const key = localStorage.key(i)
      if (key?.startsWith(PROJECT_KEY_PREFIX)) keys.push(key)
    }
    keys.forEach((k) => localStorage.removeItem(k))
  })

  describe('getProjectsIndex / setProjectsIndex', () => {
    it('getProjectsIndex returns empty array when key missing', () => {
      expect(getProjectsIndex()).toEqual([])
    })

    it('getProjectsIndex returns empty array for invalid JSON', () => {
      localStorage.setItem(PROJECTS_INDEX_KEY, 'not json')
      expect(getProjectsIndex()).toEqual([])
    })

    it('getProjectsIndex filters non-object and missing id', () => {
      localStorage.setItem(
        PROJECTS_INDEX_KEY,
        JSON.stringify([
          { id: 'a' },
          null,
          { name: 'no-id' },
          { id: 'b', updatedAt: 1 },
        ]),
      )
      expect(getProjectsIndex()).toEqual([{ id: 'a' }, { id: 'b', updatedAt: 1 }])
    })

    it('setProjectsIndex persists and getProjectsIndex reads back', () => {
      const meta = [{ id: 'p1', name: 'Proj', updatedAt: 100 }]
      setProjectsIndex(meta)
      expect(getProjectsIndex()).toEqual(meta)
    })
  })

  describe('getProjectSnapshot / setProjectSnapshot / deleteProjectSnapshot', () => {
    it('getProjectSnapshot returns null when key missing', () => {
      expect(getProjectSnapshot('missing-id')).toBeNull()
    })

    it('getProjectSnapshot returns null for invalid JSON', () => {
      localStorage.setItem(PROJECT_KEY_PREFIX + 'x', 'not json')
      expect(getProjectSnapshot('x')).toBeNull()
    })

    it('getProjectSnapshot returns null for invalid snapshot shape', () => {
      localStorage.setItem(PROJECT_KEY_PREFIX + 'x', JSON.stringify({ id: 'x' }))
      expect(getProjectSnapshot('x')).toBeNull()
    })

    it('setProjectSnapshot and getProjectSnapshot round-trip', () => {
      const snapshot = {
        id: 'proj-1',
        version: 1,
        nodes: [{ id: 'n1', position: { x: 0, y: 0 }, type: 'computation' as const, content: '1+1' }],
        edges: [{ sourceId: 'n1', targetId: 'n2', targetInputName: 'input' }],
      }
      setProjectSnapshot(snapshot)
      expect(getProjectSnapshot('proj-1')).toEqual(snapshot)
    })

    it('deleteProjectSnapshot removes snapshot', () => {
      setProjectSnapshot({ id: 'del-me', nodes: [], edges: [] })
      expect(getProjectSnapshot('del-me')).not.toBeNull()
      deleteProjectSnapshot('del-me')
      expect(getProjectSnapshot('del-me')).toBeNull()
    })
  })

  describe('buildSnapshotFromGraph', () => {
    it('builds snapshot from nodes and edges with initialContent', () => {
      const projectId = 'build-1'
      const nodes = [
        {
          id: 'n1',
          position: { x: 10, y: 20 },
          type: 'computation' as const,
          uri: 'snaq://graph/n1.sl',
          initialContent: 'x + 1',
        },
        {
          id: 'n2',
          position: { x: 100, y: 50 },
          type: 'presentation' as const,
          uri: 'snaq://graph/n2.sl',
        },
      ]
      const edges = [{ sourceId: 'n1', targetId: 'n2', targetInputName: 'input' }]
      const snapshot = buildSnapshotFromGraph(projectId, nodes, edges)
      expect(snapshot.id).toBe(projectId)
      expect(snapshot.version).toBe(1)
      expect(snapshot.nodes).toHaveLength(2)
      expect(snapshot.nodes[0]).toMatchObject({
        id: 'n1',
        position: { x: 10, y: 20 },
        type: 'computation',
        content: 'x + 1',
      })
      expect(snapshot.nodes[1]).toMatchObject({
        id: 'n2',
        position: { x: 100, y: 50 },
        type: 'presentation',
      })
      expect(snapshot.nodes[1].content).toBeUndefined()
      expect(snapshot.edges).toEqual(edges)
    })

    it('uses empty string for computation node when initialContent missing', () => {
      const nodes = [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'computation' as const,
          uri: 'snaq://graph/n1.sl',
        },
      ]
      const snapshot = buildSnapshotFromGraph('p', nodes, [])
      expect(snapshot.nodes[0].content).toBeUndefined()
    })

    it('omits content when computation node has empty content', () => {
      const nodes = [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'computation' as const,
          uri: 'snaq://graph/n1.sl',
          initialContent: '',
        },
      ]
      const snapshot = buildSnapshotFromGraph('p', nodes, [])
      expect(snapshot.nodes[0]).not.toHaveProperty('content')
    })

    it('includes inputs for computation nodes when present', () => {
      const nodes = [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'computation' as const,
          uri: 'snaq://graph/n1.sl',
          initialContent: '1 + 1',
          inputs: [{ name: 'x', type: 'Vector' }],
        },
      ]
      const snapshot = buildSnapshotFromGraph('p', nodes, [])
      expect(snapshot.nodes[0].inputs).toEqual([{ name: 'x', type: 'Vector' }])
    })
  })

  describe('getGraphStateForUndo', () => {
    it('returns deep-cloned nodes and edges with initialContent', () => {
      const nodes = [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'computation' as const,
          uri: 'snaq://graph/n1.sl',
          initialContent: '2 * 2',
        },
      ]
      const edges = [{ sourceId: 'n1', targetId: 'n2', targetInputName: 'x' }]
      const result = getGraphStateForUndo(nodes, edges)
      expect(result.nodes).toHaveLength(1)
      expect(result.nodes[0].initialContent).toBe('2 * 2')
      expect(result.edges).toEqual(edges)
      expect(result.nodes).not.toBe(nodes)
      expect(result.edges).not.toBe(edges)
    })

    it('returns independent copies so mutating result does not affect input', () => {
      const nodes = [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'presentation' as const,
          uri: 'snaq://graph/n1.sl',
        },
      ]
      const edges = [{ sourceId: 'a', targetId: 'b', targetInputName: 'in' }]
      const result = getGraphStateForUndo(nodes, edges)
      result.nodes[0].position = { x: 999, y: 999 }
      result.edges[0].targetInputName = 'other'
      expect(nodes[0].position).toEqual({ x: 0, y: 0 })
      expect(edges[0].targetInputName).toBe('in')
    })

    it('handles multiple nodes and edges', () => {
      const nodes = [
        { id: 'a', position: { x: 0, y: 0 }, type: 'computation' as const, uri: 'snaq://graph/a.sl', initialContent: '1' },
        { id: 'b', position: { x: 10, y: 10 }, type: 'presentation' as const, uri: 'snaq://graph/b.sl' },
      ]
      const edges = [
        { sourceId: 'a', targetId: 'b', targetInputName: 'x' },
        { sourceId: 'a', targetId: 'b', targetInputName: 'y' },
      ]
      const result = getGraphStateForUndo(nodes, edges)
      expect(result.nodes).toHaveLength(2)
      expect(result.edges).toHaveLength(2)
      expect(result.nodes[0].initialContent).toBe('1')
    })
  })

  describe('syncModelsToGraphNodes', () => {
    it('does not throw when given empty nodes', () => {
      expect(() => syncModelsToGraphNodes([])).not.toThrow()
    })

    it('does not throw when given computation nodes without models', () => {
      const nodes = [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'computation' as const,
          uri: 'snaq://graph/n1.sl',
          initialContent: 'x',
        },
      ]
      expect(() => syncModelsToGraphNodes(nodes)).not.toThrow()
    })

    it('does not throw when given presentation nodes', () => {
      const nodes = [
        {
          id: 'p1',
          position: { x: 0, y: 0 },
          type: 'presentation' as const,
          uri: 'snaq://graph/p1.sl',
        },
      ]
      expect(() => syncModelsToGraphNodes(nodes)).not.toThrow()
    })
  })
})
