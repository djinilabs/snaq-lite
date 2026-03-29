import { describe, expect, it } from 'vitest'
import {
  addCanvasNode,
  removeCanvasEdge,
  removeCanvasNode,
  upsertCanvasEdge,
  type CanvasDocumentState,
} from './document-state'

const baseState: CanvasDocumentState = {
  nodes: [
    { uri: 'snaq://canvas-a/node-1.sl', source: '1', params: [] },
    { uri: 'snaq://canvas-a/node-2.sl', source: '$x', params: [{ name: 'x', paramId: 'p1', typeName: 'Numeric' }] },
  ],
  edges: [],
}

describe('canvas document state', () => {
  it('adds node once by uri', () => {
    const withNode = addCanvasNode(baseState, {
      uri: 'snaq://canvas-a/node-3.sl',
      source: '$y',
      params: [{ name: 'y', paramId: 'p1', typeName: 'Numeric' }],
    })
    const duplicate = addCanvasNode(withNode, {
      uri: 'snaq://canvas-a/node-3.sl',
      source: 'ignored',
      params: [],
    })
    expect(withNode.nodes).toHaveLength(3)
    expect(duplicate.nodes).toHaveLength(3)
  })

  it('upserts edge by target param identity', () => {
    const withFirst = upsertCanvasEdge(baseState, {
      sourceUri: 'snaq://canvas-a/node-1.sl',
      targetUri: 'snaq://canvas-a/node-2.sl',
      targetParamId: 'p1',
    })
    const withReplacement = upsertCanvasEdge(withFirst, {
      sourceUri: 'snaq://canvas-a/node-3.sl',
      targetUri: 'snaq://canvas-a/node-2.sl',
      targetParamId: 'p1',
    })
    expect(withReplacement.edges).toEqual([
      {
        sourceUri: 'snaq://canvas-a/node-3.sl',
        targetUri: 'snaq://canvas-a/node-2.sl',
        targetParamId: 'p1',
      },
    ])
  })

  it('removes node and all attached edges', () => {
    const withEdges = {
      ...baseState,
      edges: [
        {
          sourceUri: 'snaq://canvas-a/node-1.sl',
          targetUri: 'snaq://canvas-a/node-2.sl',
          targetParamId: 'p1',
        },
      ],
    }
    const next = removeCanvasNode(withEdges, 'snaq://canvas-a/node-1.sl')
    expect(next.nodes.map((node) => node.uri)).toEqual(['snaq://canvas-a/node-2.sl'])
    expect(next.edges).toEqual([])
  })

  it('removes one edge by target uri/param', () => {
    const withEdges = {
      ...baseState,
      edges: [
        {
          sourceUri: 'snaq://canvas-a/node-1.sl',
          targetUri: 'snaq://canvas-a/node-2.sl',
          targetParamId: 'p1',
        },
        {
          sourceUri: 'snaq://canvas-a/node-1.sl',
          targetUri: 'snaq://canvas-a/node-2.sl',
          targetParamId: 'p2',
        },
      ],
    }
    const next = removeCanvasEdge(withEdges, 'snaq://canvas-a/node-2.sl', 'p2')
    expect(next.edges).toEqual([
      {
        sourceUri: 'snaq://canvas-a/node-1.sl',
        targetUri: 'snaq://canvas-a/node-2.sl',
        targetParamId: 'p1',
      },
    ])
  })
})

