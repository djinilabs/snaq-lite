import { describe, it, expect, beforeEach, vi } from 'vitest'
import { useGraphStore } from '~/store'
import { performUndo, performRedo } from './perform-undo-redo'
import { syncLoadedGraphToLsp } from '~/lib/sync-graph-to-lsp'
import { syncModelsToGraphNodes } from '~/lib/project-storage'

vi.mock('~/lib/sync-graph-to-lsp', () => ({
  syncLoadedGraphToLsp: vi.fn().mockResolvedValue(undefined),
}))

vi.mock('~/lib/project-storage', async (importOriginal) => {
  const actual = await importOriginal<typeof import('~/lib/project-storage')>()
  return {
    ...actual,
    syncModelsToGraphNodes: vi.fn(),
  }
})

/** Sets undo getter and adds two computation nodes (a, b) with one edge a→b. */
function setUpTwoNodesWithEdge(): void {
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
  useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputIndex: 0 })
}

describe('perform-undo-redo', () => {
  beforeEach(() => {
    vi.mocked(syncLoadedGraphToLsp).mockClear()
    vi.mocked(syncModelsToGraphNodes).mockClear()
    useGraphStore.setState({
      nodes: [],
      edges: [],
      pendingEdge: null,
      undoStack: [],
      redoStack: [],
      undoSnapshotGetter: null,
    })
  })

  describe('performUndo', () => {
    it('after removeEdge restores edge and calls syncLoadedGraphToLsp so LSP gets graph/connect', () => {
      setUpTwoNodesWithEdge()
      expect(useGraphStore.getState().edges).toHaveLength(1)

      useGraphStore.getState().removeEdge('b', 0)
      expect(useGraphStore.getState().edges).toHaveLength(0)

      performUndo()

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(syncLoadedGraphToLsp).toHaveBeenCalledTimes(1)
      const [nodes, edges] = vi.mocked(syncLoadedGraphToLsp).mock.calls[0]!
      expect(nodes).toHaveLength(2)
      expect(edges).toHaveLength(1)
      expect(edges[0]).toMatchObject({ sourceId: 'a', targetId: 'b', targetInputIndex: 0 })
      expect(edges[0].sourceHandle).toBe('output')
    })

    it('when undo stack is empty leaves state unchanged and still calls sync with current state', () => {
      useGraphStore.getState().addNode({
        id: 'n1',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/n1.sl',
      })
      const nodesBefore = useGraphStore.getState().nodes.length
      performUndo()
      expect(useGraphStore.getState().nodes).toHaveLength(nodesBefore)
      expect(syncLoadedGraphToLsp).toHaveBeenCalledTimes(1)
      const [nodes, edges] = vi.mocked(syncLoadedGraphToLsp).mock.calls[0]!
      expect(nodes).toHaveLength(1)
      expect(edges).toHaveLength(0)
    })

    it('with multiple edges restored calls sync with full restored graph after two undos', () => {
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
      useGraphStore.getState().addNode({
        id: 'c',
        position: { x: 200, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/c.sl',
      })
      useGraphStore.getState().addEdge({ sourceId: 'a', targetId: 'b', targetInputIndex: 0 })
      useGraphStore.getState().addEdge({ sourceId: 'b', targetId: 'c', targetInputIndex: 0 })
      expect(useGraphStore.getState().edges).toHaveLength(2)

      useGraphStore.getState().removeEdge('c', 0)
      useGraphStore.getState().removeEdge('b', 0)
      expect(useGraphStore.getState().edges).toHaveLength(0)

      performUndo()
      expect(useGraphStore.getState().edges).toHaveLength(1)
      performUndo()

      expect(useGraphStore.getState().edges).toHaveLength(2)
      expect(syncLoadedGraphToLsp).toHaveBeenCalledTimes(2)
      const [nodes, edges] = vi.mocked(syncLoadedGraphToLsp).mock.calls[1]!
      expect(nodes).toHaveLength(3)
      expect(edges).toHaveLength(2)
    })
  })

  describe('performRedo', () => {
    it('calls syncLoadedGraphToLsp with current nodes and edges', () => {
      setUpTwoNodesWithEdge()
      useGraphStore.getState().undo()
      expect(useGraphStore.getState().edges).toHaveLength(0)

      performRedo()

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(syncLoadedGraphToLsp).toHaveBeenCalledTimes(1)
      const [, edges] = vi.mocked(syncLoadedGraphToLsp).mock.calls[0]!
      expect(edges).toHaveLength(1)
    })

    it('when redo stack is empty leaves state unchanged and still calls sync with current state', () => {
      useGraphStore.getState().addNode({
        id: 'n1',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/n1.sl',
      })
      const nodesBefore = useGraphStore.getState().nodes.length
      performRedo()
      expect(useGraphStore.getState().nodes).toHaveLength(nodesBefore)
      expect(syncLoadedGraphToLsp).toHaveBeenCalledTimes(1)
      const [nodes, edges] = vi.mocked(syncLoadedGraphToLsp).mock.calls[0]!
      expect(nodes).toHaveLength(1)
      expect(edges).toHaveLength(0)
    })
  })

  describe('sync steps', () => {
    it('calls syncModelsToGraphNodes before syncLoadedGraphToLsp', () => {
      setUpTwoNodesWithEdge()
      useGraphStore.getState().removeEdge('b', 0)
      performUndo()
      const modelOrder = vi.mocked(syncModelsToGraphNodes).mock.invocationCallOrder[0]
      const lspOrder = vi.mocked(syncLoadedGraphToLsp).mock.invocationCallOrder[0]
      expect(modelOrder).toBeLessThan(lspOrder!)
    })

    it('calls syncModelsToGraphNodes with restored nodes after performUndo', () => {
      setUpTwoNodesWithEdge()
      useGraphStore.getState().removeEdge('b', 0)
      performUndo()
      expect(syncModelsToGraphNodes).toHaveBeenCalledTimes(1)
      const [nodes] = vi.mocked(syncModelsToGraphNodes).mock.calls[0]!
      expect(nodes).toHaveLength(2)
      expect(nodes.map((n) => n.id)).toEqual(['a', 'b'])
    })

    it('calls syncModelsToGraphNodes with restored nodes after performRedo', () => {
      setUpTwoNodesWithEdge()
      useGraphStore.getState().undo()
      performRedo()
      expect(syncModelsToGraphNodes).toHaveBeenCalledTimes(1)
      const [nodes] = vi.mocked(syncModelsToGraphNodes).mock.calls[0]!
      expect(nodes).toHaveLength(2)
    })
  })
})
