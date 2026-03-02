import { describe, it, expect, vi } from 'vitest'
import { getFlowNodeData } from './graph-node-data'
import { applyNodePositionChanges } from './graph-node-position-changes'
import type { GraphNode, GraphEdge } from '~/store'

describe('getFlowNodeData', () => {
  const compNode: GraphNode = {
    id: 'comp-1',
    position: { x: 0, y: 0 },
    type: 'computation',
    uri: 'snaq://graph/comp-1.sl',
  }

  const presNode: GraphNode = {
    id: 'pres-1',
    position: { x: 200, y: 0 },
    type: 'presentation',
    uri: 'snaq://graph/pres-1.sl',
  }

  it('sets sourceUri to empty for presentation node when no edge targets it', () => {
    const nodes: GraphNode[] = [compNode, presNode]
    const edges: GraphEdge[] = []
    const data = getFlowNodeData(presNode, nodes, edges)
    expect(data.sourceUri).toBe('')
  })

  it('sets sourceUri to source node uri for presentation node when edge connects computation to it', () => {
    const nodes: GraphNode[] = [compNode, presNode]
    const edges: GraphEdge[] = [
      { sourceId: 'comp-1', targetId: 'pres-1', targetInputName: 'input' },
    ]
    const data = getFlowNodeData(presNode, nodes, edges)
    expect(data.sourceUri).toBe('snaq://graph/comp-1.sl')
  })

  it('sets sourceUri to n.uri for computation node', () => {
    const nodes: GraphNode[] = [compNode]
    const edges: GraphEdge[] = []
    const data = getFlowNodeData(compNode, nodes, edges)
    expect(data.sourceUri).toBe('snaq://graph/comp-1.sl')
  })

  it('sets sourceUri to empty for presentation node when edge exists but source node not in store', () => {
    const nodes: GraphNode[] = [presNode]
    const edges: GraphEdge[] = [
      { sourceId: 'comp-missing', targetId: 'pres-1', targetInputName: 'input' },
    ]
    const data = getFlowNodeData(presNode, nodes, edges)
    expect(data.sourceUri).toBe('')
  })
})

describe('applyNodePositionChanges', () => {
  it('on position change with dragging true updates only live positions, does not call moveNode', () => {
    const moveNode = vi.fn()
    const setLivePositions = vi.fn()
    applyNodePositionChanges(
      [
        {
          type: 'position',
          id: 'n1',
          position: { x: 50, y: 60 },
          dragging: true,
        },
      ],
      moveNode,
      setLivePositions,
    )
    expect(moveNode).not.toHaveBeenCalled()
    expect(setLivePositions).toHaveBeenCalledTimes(1)
    const updater = setLivePositions.mock.calls[0][0]
    expect(typeof updater).toBe('function')
    expect(updater({})).toEqual({ n1: { x: 50, y: 60 } })
  })

  it('on position change with dragging false calls moveNode and clears live position for that node', () => {
    const moveNode = vi.fn()
    const setLivePositions = vi.fn()
    applyNodePositionChanges(
      [
        {
          type: 'position',
          id: 'n1',
          position: { x: 100, y: 200 },
          dragging: false,
        },
      ],
      moveNode,
      setLivePositions,
    )
    expect(moveNode).toHaveBeenCalledTimes(1)
    expect(moveNode).toHaveBeenCalledWith('n1', { x: 100, y: 200 })
    expect(setLivePositions).toHaveBeenCalledTimes(1)
    const updater = setLivePositions.mock.calls[0][0]
    expect(updater({ n1: { x: 50, y: 60 } })).toEqual({})
  })

  it('drag then drop: store updated only on drop with final position', () => {
    const moveNode = vi.fn()
    const setLivePositions = vi.fn()
    applyNodePositionChanges(
      [
        { type: 'position', id: 'n1', position: { x: 10, y: 20 }, dragging: true },
        { type: 'position', id: 'n1', position: { x: 30, y: 40 }, dragging: true },
      ],
      moveNode,
      setLivePositions,
    )
    expect(moveNode).not.toHaveBeenCalled()
    applyNodePositionChanges(
      [
        { type: 'position', id: 'n1', position: { x: 30, y: 40 }, dragging: false },
      ],
      moveNode,
      setLivePositions,
    )
    expect(moveNode).toHaveBeenCalledTimes(1)
    expect(moveNode).toHaveBeenCalledWith('n1', { x: 30, y: 40 })
  })
})
