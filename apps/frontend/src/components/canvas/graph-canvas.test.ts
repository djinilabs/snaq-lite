import { describe, it, expect } from 'vitest'
import { getFlowNodeData } from './graph-node-data'
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
