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

  it('returns targetUri and targetInputIndex for each deleted edge with matching node and numeric handle', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'n2', targetHandle: '0' },
      { target: 'n1', targetHandle: '1' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([
      { targetUri: 'snaq://graph/n2.sl', targetInputIndex: 0 },
      { targetUri: 'snaq://graph/n1.sl', targetInputIndex: 1 },
    ])
  })

  it('omits edges whose target node is not in nodes', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'missing', targetHandle: '0' },
      { target: 'n2', targetHandle: '0' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([{ targetUri: 'snaq://graph/n2.sl', targetInputIndex: 0 }])
  })

  it('omits edges without a valid numeric targetHandle', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'n2', targetHandle: undefined },
      { target: 'n2', targetHandle: null },
      { target: 'n2', targetHandle: '0' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([{ targetUri: 'snaq://graph/n2.sl', targetInputIndex: 0 }])
  })

  it('omits edges when targetHandle is non-numeric string', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'n2', targetHandle: 'x' },
      { target: 'n1', targetHandle: '0' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([{ targetUri: 'snaq://graph/n1.sl', targetInputIndex: 0 }])
  })

  it('omits edges when targetHandle is negative or non-integer', () => {
    const deleted: DeletedEdgeLike[] = [
      { target: 'n2', targetHandle: '-1' },
      { target: 'n2', targetHandle: '1.5' },
      { target: 'n1', targetHandle: '0' },
    ]
    const result = getDisconnectParamsForDeletedEdges(deleted, nodes)
    expect(result).toEqual([{ targetUri: 'snaq://graph/n1.sl', targetInputIndex: 0 }])
  })

  it('returns empty array when deleted is empty', () => {
    expect(getDisconnectParamsForDeletedEdges([], nodes)).toEqual([])
  })

  it('returns empty array when nodes is empty', () => {
    const deleted: DeletedEdgeLike[] = [{ target: 'n1', targetHandle: '0' }]
    expect(getDisconnectParamsForDeletedEdges(deleted, [])).toEqual([])
  })
})
