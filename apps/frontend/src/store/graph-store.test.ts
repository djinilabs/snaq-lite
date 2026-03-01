import { describe, it, expect, beforeEach } from 'vitest'
import { useGraphStore } from './graph-store'

describe('graph-store', () => {
  beforeEach(() => {
    useGraphStore.setState({
      nodes: [],
      edges: [],
      pendingEdge: null,
      focusEditorForNodeId: null,
    })
  })

  it('addNode appends node with undefined inputs/outputType', () => {
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0]).toMatchObject({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().nodes[0].inputs).toBeUndefined()
    expect(useGraphStore.getState().nodes[0].outputType).toBeUndefined()
  })

  it('addNode sets focusEditorForNodeId for computation type', () => {
    useGraphStore.getState().addNode({
      id: 'c1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/c1.sl',
    })
    expect(useGraphStore.getState().focusEditorForNodeId).toBe('c1')
  })

  it('addNode does not set focusEditorForNodeId for presentation type', () => {
    useGraphStore.setState({ focusEditorForNodeId: null })
    useGraphStore.getState().addNode({
      id: 'p1',
      position: { x: 0, y: 0 },
      type: 'presentation',
      uri: 'snaq://graph/p1.sl',
    })
    expect(useGraphStore.getState().focusEditorForNodeId).toBeNull()
  })

  it('moveNode updates position for matching id', () => {
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().moveNode('n1', { x: 10, y: 20 })
    expect(useGraphStore.getState().nodes[0].position).toEqual({ x: 10, y: 20 })
  })

  it('removeNode removes node and edges involving it', () => {
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().addNode({
      id: 'n2',
      position: { x: 100, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n2.sl',
    })
    useGraphStore.getState().addEdge({ sourceId: 'n1', targetId: 'n2', targetInputName: 'x' })
    useGraphStore.getState().removeNode('n1')
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().edges).toHaveLength(0)
  })

  it('addEdge replaces existing edge for same target and input', () => {
    useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputName: 'x' })
    useGraphStore.getState().addEdge({ sourceId: 'c', targetId: 'b', targetInputName: 'x' })
    expect(useGraphStore.getState().edges).toHaveLength(1)
    expect(useGraphStore.getState().edges[0].sourceId).toBe('c')
  })

  it('addEdge clears pendingEdge', () => {
    useGraphStore.getState().setPendingEdge({
      sourceId: 'a',
      sourceHandle: null,
      targetPosition: { x: 1, y: 1 },
    })
    useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputName: 'x' })
    expect(useGraphStore.getState().pendingEdge).toBeNull()
  })

  it('removeEdge removes matching edge', () => {
    useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputName: 'x' })
    useGraphStore.getState().removeEdge('b', 'x')
    expect(useGraphStore.getState().edges).toHaveLength(0)
  })

  it('setPendingEdge and clearPendingEdge', () => {
    const pending = { sourceId: 'a', sourceHandle: 'out' as string | null, targetPosition: { x: 0, y: 0 } }
    useGraphStore.getState().setPendingEdge(pending)
    expect(useGraphStore.getState().pendingEdge).toEqual(pending)
    useGraphStore.getState().clearPendingEdge()
    expect(useGraphStore.getState().pendingEdge).toBeNull()
  })

  it('applyNodeSignature updates node with matching uri', () => {
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().applyNodeSignature(
      'snaq://graph/n1.sl',
      [{ name: 'x', type: 'Vector' }],
      'Numeric',
    )
    expect(useGraphStore.getState().nodes[0].inputs).toBeUndefined()
    expect(useGraphStore.getState().nodes[0].outputType).toBe('Numeric')
  })

  it('applyNodeSignature with null outputType', () => {
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().applyNodeSignature('snaq://graph/n1.sl', [], null)
    expect(useGraphStore.getState().nodes[0].outputType).toBeNull()
  })

  it('setNodeInputs updates inputs for the node', () => {
    useGraphStore.setState({ nodes: [], edges: [] })
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().nodes[0].inputs).toBeUndefined()
    useGraphStore.getState().setNodeInputs('n1', [{ name: 'x', type: 'Vector' }])
    expect(useGraphStore.getState().nodes[0].inputs).toEqual([{ name: 'x', type: 'Vector' }])
    useGraphStore.getState().setNodeInputs('n1', [
      { name: 'a', type: 'Numeric' },
      { name: 'b', type: 'Vector' },
    ])
    expect(useGraphStore.getState().nodes[0].inputs).toEqual([
      { name: 'a', type: 'Numeric' },
      { name: 'b', type: 'Vector' },
    ])
  })

  it('setGraph clears focusEditorForNodeId', () => {
    useGraphStore.setState({ focusEditorForNodeId: 'some-id' })
    useGraphStore.getState().setGraph([], [])
    expect(useGraphStore.getState().focusEditorForNodeId).toBeNull()
  })

  it('setGraph replaces nodes and edges and clears pendingEdge', () => {
    useGraphStore.getState().addNode({
      id: 'old',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/old.sl',
    })
    useGraphStore.getState().setPendingEdge({
      sourceId: 'old',
      sourceHandle: null,
      targetPosition: { x: 1, y: 1 },
    })
    const nodes = [
      {
        id: 'a',
        position: { x: 10, y: 20 },
        type: 'computation' as const,
        uri: 'snaq://graph/a.sl',
      },
    ]
    const edges = [{ sourceId: 'a', targetId: 'b', targetInputName: 'x' }]
    useGraphStore.getState().setGraph(nodes, edges)
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0]).toMatchObject({ id: 'a', position: { x: 10, y: 20 } })
    expect(useGraphStore.getState().edges).toEqual(edges)
    expect(useGraphStore.getState().pendingEdge).toBeNull()
  })

  it('setGraph preserves initialContent on nodes', () => {
    const nodes = [
      {
        id: 'n1',
        position: { x: 0, y: 0 },
        type: 'computation' as const,
        uri: 'snaq://graph/n1.sl',
        initialContent: '2 + 2',
      },
    ]
    useGraphStore.getState().setGraph(nodes, [])
    expect(useGraphStore.getState().nodes[0].initialContent).toBe('2 + 2')
  })
})
