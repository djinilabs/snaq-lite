import { describe, it, expect } from 'vitest'
import {
  getDisconnectParamsForDeletedEdges,
  type DeletedEdgeLike,
  type NodeLike,
} from './edge-delete-params'

describe('getDisconnectParamsForDeletedEdges', () => {
  const nodes: NodeLike[] = [
    { id: 'n1', uri: 'snaq://graph/n1.sl' },
    { id: 'n2', uri: 'snaq://graph/n2.sl' },
  ]

  it('returns targetUri and targetInputName for each deleted edge with matching node and string handle', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'n2', targetHandle: 'x' },
      { target: 'n1', targetHandle: 'y' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([
      { targetUri: 'snaq://graph/n2.sl', targetInputName: 'x' },
      { targetUri: 'snaq://graph/n1.sl', targetInputName: 'y' },
    ])
  })

  it('omits edges whose target node is not in nodes', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'missing', targetHandle: 'x' },
      { target: 'n2', targetHandle: 'x' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([{ targetUri: 'snaq://graph/n2.sl', targetInputName: 'x' }])
  })

  it('omits edges without a string targetHandle', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'n2', targetHandle: undefined },
      { target: 'n2', targetHandle: null },
      { target: 'n2', targetHandle: 'x' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([{ targetUri: 'snaq://graph/n2.sl', targetInputName: 'x' }])
  })

  it('returns empty array when deleted is empty', () => {
    expect(getDisconnectParamsForDeletedEdges([], nodes)).toEqual([])
  })

  it('returns empty array when nodes is empty', () => {
    const deleted: DeletedEdgeLike[] = [{ target: 'n1', targetHandle: 'x' }]
    expect(getDisconnectParamsForDeletedEdges(deleted, [])).toEqual([])
  })
})
