import { describe, it, expect, beforeEach, vi } from 'vitest'
import { connectEdge, disconnectEdge } from './edge-handlers'
import { useGraphStore } from '~/store'
import { useUIStore } from '~/store'
import { LSP_METHOD_GRAPH_CONNECT, LSP_METHOD_GRAPH_DISCONNECT } from '~/lib/constants'

const mockSendRequest = vi.fn()
const mockHasLanguageClient = vi.fn(() => true)
const mockClient = { sendRequest: mockSendRequest, sendNotification: vi.fn() }
vi.mock('~/lsp/language-client-singleton', () => ({
  waitForLanguageClient: () =>
    mockHasLanguageClient()
      ? Promise.resolve(mockClient)
      : Promise.resolve(null),
}))

describe('edge-handlers', () => {
  beforeEach(() => {
    mockSendRequest.mockReset()
    mockHasLanguageClient.mockReturnValue(true)
    useGraphStore.setState({ nodes: [], edges: [], pendingEdge: null })
  })

  describe('connectEdge', () => {
    it('adds edge to store, calls LSP connect, and returns true on success', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      mockSendRequest.mockResolvedValue(undefined)

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 0)

      expect(result).toBe(true)
      expect(mockSendRequest).toHaveBeenCalledTimes(1)
      expect(mockSendRequest).toHaveBeenCalledWith(LSP_METHOD_GRAPH_CONNECT, {
        sourceUri: 'snaq://graph/n1.sl',
        targetUri: 'snaq://graph/n2.sl',
        targetInputName: 'x',
      })
      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(useGraphStore.getState().edges[0]).toEqual({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })
    })

    it('on LSP error removes edge, clears pendingEdge, adds toast, and returns false', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      mockSendRequest.mockRejectedValue(new Error('Type mismatch'))
      const addToast = vi.fn()
      useUIStore.setState({ addToast })
      useGraphStore.getState().setPendingEdge({
        sourceId: 'n1',
        sourceHandle: 'output',
        targetPosition: null,
      })

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 0)

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(useGraphStore.getState().pendingEdge).toBeNull()
      expect(addToast).toHaveBeenCalledWith('Type mismatch', 'error')
    })

    it('returns false and does not add edge or call LSP when client not ready', async () => {
      mockHasLanguageClient.mockReturnValue(false)
      const addToast = vi.fn()
      useUIStore.setState({ addToast })
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 0)

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(mockSendRequest).not.toHaveBeenCalled()
      expect(addToast).toHaveBeenCalledWith(
        'Editor is still loading. Please try again in a moment.',
        'error',
      )
    })

    it('returns false and does not call LSP when source or target node is missing', async () => {
      useGraphStore.getState().addNode({
        id: 'n1',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/n1.sl',
      })
      useGraphStore.getState().setNodeInputs('n1', [{ name: 'x', type: 'Vector' }])

      expect(await connectEdge('snaq://graph/n1.sl', 'snaq://graph/missing.sl', 0)).toBe(false)
      expect(await connectEdge('snaq://graph/missing.sl', 'snaq://graph/n1.sl', 0)).toBe(false)
      expect(mockSendRequest).not.toHaveBeenCalled()
    })

    it('returns false and toasts when target input index is out of range', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 1)

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(mockSendRequest).not.toHaveBeenCalled()
      expect(addToast).toHaveBeenCalledWith('Target input not found or has no name.', 'error')
    })

    it('returns false and toasts when target input at index has empty name', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: '  ', type: 'Numeric' }])
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 0)

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(mockSendRequest).not.toHaveBeenCalled()
      expect(addToast).toHaveBeenCalledWith('Target input not found or has no name.', 'error')
    })

    it('on non-Error throw still removes edge and toasts string representation', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      mockSendRequest.mockRejectedValue('Server unavailable')
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 0)

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(addToast).toHaveBeenCalledWith('Server unavailable', 'error')
    })
  })

  describe('disconnectEdge', () => {
    it('shows toast and does not remove edge when client not ready', async () => {
      mockHasLanguageClient.mockReturnValue(false)
      const addToast = vi.fn()
      useUIStore.setState({ addToast })
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })

      await disconnectEdge('snaq://graph/n2.sl', 0)

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(mockSendRequest).not.toHaveBeenCalled()
      expect(addToast).toHaveBeenCalledWith(
        'Editor is still loading. Please try again in a moment.',
        'error',
      )
    })

    it('calls LSP disconnect and removes edge from store', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })
      mockSendRequest.mockResolvedValue(undefined)

      await disconnectEdge('snaq://graph/n2.sl', 0)

      expect(mockSendRequest).toHaveBeenCalledTimes(1)
      expect(mockSendRequest).toHaveBeenCalledWith(LSP_METHOD_GRAPH_DISCONNECT, {
        targetUri: 'snaq://graph/n2.sl',
        targetInputName: 'x',
      })
      expect(useGraphStore.getState().edges).toHaveLength(0)
    })

    it('sends current target input name at index to LSP (rename-before-disconnect uses new name)', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'oldName', type: 'Vector' }])
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'newName', type: 'Vector' }])
      mockSendRequest.mockResolvedValue(undefined)

      await disconnectEdge('snaq://graph/n2.sl', 0)

      expect(mockSendRequest).toHaveBeenCalledWith(LSP_METHOD_GRAPH_DISCONNECT, {
        targetUri: 'snaq://graph/n2.sl',
        targetInputName: 'newName',
      })
      expect(useGraphStore.getState().edges).toHaveLength(0)
    })

    it('on LSP error rolls back edge and adds toast', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })
      mockSendRequest.mockRejectedValue(new Error('LSP disconnect failed'))
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      await disconnectEdge('snaq://graph/n2.sl', 0)

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(useGraphStore.getState().edges[0]).toEqual({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })
      expect(addToast).toHaveBeenCalledWith('LSP disconnect failed', 'error')
    })

    it('does nothing when target node not in store', async () => {
      await disconnectEdge('snaq://graph/missing.sl', 0)
      expect(mockSendRequest).not.toHaveBeenCalled()
    })

    it('on non-Error throw still rolls back and toasts string representation', async () => {
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
      useGraphStore.getState().setNodeInputs('n2', [{ name: 'x', type: 'Vector' }])
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputIndex: 0,
      })
      mockSendRequest.mockRejectedValue('Network error')
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      await disconnectEdge('snaq://graph/n2.sl', 0)

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(addToast).toHaveBeenCalledWith('Network error', 'error')
    })
  })
})
