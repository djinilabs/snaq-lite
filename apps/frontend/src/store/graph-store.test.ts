import { describe, it, expect, beforeEach } from 'vitest'
import { UNDO_STACK_MAX } from '~/lib/constants'
import { useGraphStore } from './graph-store'

describe('graph-store', () => {
  beforeEach(() => {
    useGraphStore.setState({
      nodes: [],
      edges: [],
      pendingEdge: null,
      focusEditorForNodeId: null,
      undoStack: [],
      redoStack: [],
      undoSnapshotGetter: null,
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

  it('when getter is not set, mutators do not push to undo (no crash)', () => {
    expect(useGraphStore.getState().undoSnapshotGetter).toBeNull()
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().undoStack).toHaveLength(0)
  })

  it('when getter is set, addNode pushes to undo and undo restores previous state', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().undoStack).toHaveLength(1)
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes).toHaveLength(0)
    expect(useGraphStore.getState().undoStack).toHaveLength(0)
    expect(useGraphStore.getState().redoStack).toHaveLength(1)
  })

  it('redo restores state after undo', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes).toHaveLength(0)
    useGraphStore.getState().redo()
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0].id).toBe('n1')
  })

  it('setGraph with clearHistory: true clears undo and redo stacks', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().undoStack).toHaveLength(1)
    useGraphStore.getState().setGraph([], [], { clearHistory: true })
    expect(useGraphStore.getState().undoStack).toHaveLength(0)
    expect(useGraphStore.getState().redoStack).toHaveLength(0)
  })

  it('undo stack is capped at UNDO_STACK_MAX (10)', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    for (let i = 0; i < 15; i++) {
      useGraphStore.getState().addNode({
        id: `n${i}`,
        position: { x: i * 10, y: 0 },
        type: 'computation',
        uri: `snaq://graph/n${i}.sl`,
      })
    }
    expect(useGraphStore.getState().undoStack.length).toBeLessThanOrEqual(UNDO_STACK_MAX)
    expect(useGraphStore.getState().undoStack.length).toBe(UNDO_STACK_MAX)
  })

  it('applyNodeSignature does not push to undo stack', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    const lenBefore = useGraphStore.getState().undoStack.length
    useGraphStore.getState().applyNodeSignature('snaq://graph/n1.sl', [], 'Numeric')
    expect(useGraphStore.getState().undoStack.length).toBe(lenBefore)
  })

  it('when getter is set, moveNode pushes to undo and undo restores position', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().moveNode('n1', { x: 100, y: 200 })
    expect(useGraphStore.getState().nodes[0].position).toEqual({ x: 100, y: 200 })
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0].position).toEqual({ x: 0, y: 0 })
  })

  it('when getter is set, removeEdge pushes to undo', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputName: 'x' })
    expect(useGraphStore.getState().undoStack).toHaveLength(1)
    useGraphStore.getState().removeEdge('b', 'x')
    expect(useGraphStore.getState().undoStack).toHaveLength(2)
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().edges).toHaveLength(1)
  })

  it('undo when undoStack is empty leaves state unchanged', () => {
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    const nodesBefore = useGraphStore.getState().nodes.length
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes).toHaveLength(nodesBefore)
  })

  it('redo when redoStack is empty leaves state unchanged', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes).toHaveLength(0)
    useGraphStore.getState().redo()
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    useGraphStore.getState().redo()
    expect(useGraphStore.getState().nodes).toHaveLength(1)
  })

  it('when getter is set, removeNode pushes to undo and undo restores node', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().undoStack).toHaveLength(1)
    useGraphStore.getState().removeNode('n1')
    expect(useGraphStore.getState().nodes).toHaveLength(0)
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0].id).toBe('n1')
  })

  it('when getter is set, addEdge pushes to undo and undo removes edge', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'a',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/a.sl',
    })
    useGraphStore.getState().addNode({
      id: 'b',
      position: { x: 100, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/b.sl',
    })
    useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputName: 'x' })
    expect(useGraphStore.getState().edges).toHaveLength(1)
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().edges).toHaveLength(0)
  })

  it('when getter is set, setNodeInputs pushes to undo and undo restores previous inputs', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().setNodeInputs('n1', [{ name: 'x', type: 'Numeric' }])
    expect(useGraphStore.getState().nodes[0].inputs).toHaveLength(1)
    useGraphStore.getState().setNodeInputs('n1', [
      { name: 'x', type: 'Numeric' },
      { name: 'y', type: 'Vector' },
    ])
    expect(useGraphStore.getState().nodes[0].inputs).toHaveLength(2)
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().nodes[0].inputs).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0].inputs?.[0].name).toBe('x')
  })

  it('when getter throws, mutator does not push (undo stack unchanged)', () => {
    const getter = () => {
      throw new Error('getter error')
    }
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    expect(useGraphStore.getState().undoStack).toHaveLength(0)
    expect(useGraphStore.getState().nodes).toHaveLength(1)
  })

  it('setGraph without clearHistory preserves undo and redo stacks', () => {
    const getter = () => ({
      nodes: [...useGraphStore.getState().nodes],
      edges: [...useGraphStore.getState().edges],
    })
    useGraphStore.getState().setUndoSnapshotGetter(getter)
    useGraphStore.getState().addNode({
      id: 'n1',
      position: { x: 0, y: 0 },
      type: 'computation',
      uri: 'snaq://graph/n1.sl',
    })
    useGraphStore.getState().undo()
    expect(useGraphStore.getState().undoStack).toHaveLength(0)
    expect(useGraphStore.getState().redoStack).toHaveLength(1)
    const newNodes = [
      {
        id: 'n2',
        position: { x: 10, y: 10 },
        type: 'computation' as const,
        uri: 'snaq://graph/n2.sl',
      },
    ]
    useGraphStore.getState().setGraph(newNodes, [])
    expect(useGraphStore.getState().nodes).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0].id).toBe('n2')
    expect(useGraphStore.getState().undoStack).toHaveLength(0)
    expect(useGraphStore.getState().redoStack).toHaveLength(1)
  })
})
