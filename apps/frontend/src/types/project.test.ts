import { describe, it, expect } from 'vitest'
import { parseProjectSnapshot } from './project'

describe('parseProjectSnapshot', () => {
  it('returns null for non-object', () => {
    expect(parseProjectSnapshot(null)).toBeNull()
    expect(parseProjectSnapshot(undefined)).toBeNull()
    expect(parseProjectSnapshot('')).toBeNull()
    expect(parseProjectSnapshot(1)).toBeNull()
  })

  it('returns null when id or nodes or edges missing', () => {
    expect(parseProjectSnapshot({})).toBeNull()
    expect(parseProjectSnapshot({ id: 'x' })).toBeNull()
    expect(parseProjectSnapshot({ id: 'x', nodes: [] })).toBeNull()
    expect(parseProjectSnapshot({ id: 'x', edges: [] })).toBeNull()
    expect(parseProjectSnapshot({ nodes: [], edges: [] })).toBeNull()
  })

  it('parses valid minimal snapshot', () => {
    const snapshot = parseProjectSnapshot({
      id: 'proj-1',
      nodes: [],
      edges: [],
    })
    expect(snapshot).toEqual({ id: 'proj-1', nodes: [], edges: [] })
  })

  it('parses nodes with position and type', () => {
    const snapshot = parseProjectSnapshot({
      id: 'p',
      nodes: [
        { id: 'n1', position: { x: 0, y: 0 }, type: 'computation' },
        { id: 'n2', position: { x: 100, y: 50 }, type: 'presentation', content: 'x' },
      ],
      edges: [],
    })
    expect(snapshot?.nodes).toHaveLength(2)
    expect(snapshot?.nodes[0]).toEqual({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      content: undefined,
    })
    expect(snapshot?.nodes[1]).toEqual({
      id: 'n2',
      position: { x: 100, y: 50 },
      type: 'presentation',
      content: 'x',
    })
  })

  it('parses computation nodes with inputs', () => {
    const snapshot = parseProjectSnapshot({
      id: 'p',
      nodes: [
        {
          id: 'n1',
          position: { x: 0, y: 0 },
          type: 'computation',
          inputs: [
            { name: 'x', type: 'Vector' },
            { name: 'y', type: 'Numeric' },
          ],
        },
      ],
      edges: [],
    })
    expect(snapshot?.nodes[0].inputs).toEqual([
      { name: 'x', type: 'Vector' },
      { name: 'y', type: 'Numeric' },
    ])
  })

  it('parses edges with targetInputIndex', () => {
    const snapshot = parseProjectSnapshot({
      id: 'p',
      nodes: [],
      edges: [{ sourceId: 'a', targetId: 'b', targetInputIndex: 0 }],
    })
    expect(snapshot?.edges).toEqual([
      { sourceId: 'a', targetId: 'b', targetInputIndex: 0 },
    ])
  })

  it('parses edges with legacy targetInputName', () => {
    const snapshot = parseProjectSnapshot({
      id: 'p',
      nodes: [],
      edges: [{ sourceId: 'a', targetId: 'b', targetInputName: 'input' }],
    })
    expect(snapshot?.edges).toEqual([
      { sourceId: 'a', targetId: 'b', targetInputName: 'input' },
    ])
  })

  it('returns null for invalid node type', () => {
    expect(
      parseProjectSnapshot({
        id: 'p',
        nodes: [{ id: 'n', position: { x: 0, y: 0 }, type: 'invalid' }],
        edges: [],
      }),
    ).toBeNull()
  })

  it('returns null for invalid node position', () => {
    expect(
      parseProjectSnapshot({
        id: 'p',
        nodes: [{ id: 'n', position: { x: '0', y: 0 }, type: 'computation' }],
        edges: [],
      }),
    ).toBeNull()
  })

  it('returns null for invalid edge shape (missing both targetInputIndex and targetInputName)', () => {
    expect(
      parseProjectSnapshot({
        id: 'p',
        nodes: [],
        edges: [{ sourceId: 'a', targetId: 'b' }],
      }),
    ).toBeNull()
  })
})
