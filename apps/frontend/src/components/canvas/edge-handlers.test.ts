import { describe, it, expect, beforeEach, vi } from 'vitest'
import { connectEdge, disconnectEdge } from './edge-handlers'
import { useGraphStore } from '~/store'
import { useUIStore } from '~/store'
import { LSP_METHOD_GRAPH_CONNECT, LSP_METHOD_GRAPH_DISCONNECT } from '~/lib/constants'

const mockSendRequest = vi.fn()
vi.mock('~/lsp/language-client-singleton', () => ({
  getLanguageClient: () => ({
    sendRequest: mockSendRequest,
    sendNotification: vi.fn(),
  }),
}))

describe('edge-handlers', () => {
  beforeEach(() => {
    mockSendRequest.mockReset()
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
      mockSendRequest.mockResolvedValue(undefined)

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 'x')

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
        targetInputName: 'x',
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
      mockSendRequest.mockRejectedValue(new Error('Type mismatch'))
      const addToast = vi.fn()
      useUIStore.setState({ addToast })
      useGraphStore.getState().setPendingEdge({
        sourceId: 'n1',
        sourceHandle: 'output',
        targetPosition: null,
      })

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 'x')

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(useGraphStore.getState().pendingEdge).toBeNull()
      expect(addToast).toHaveBeenCalledWith('Type mismatch', 'error')
    })

    it('returns false and does not call LSP when source or target node is missing', async () => {
      useGraphStore.getState().addNode({
        id: 'n1',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/n1.sl',
      })

      expect(await connectEdge('snaq://graph/n1.sl', 'snaq://graph/missing.sl', 'x')).toBe(false)
      expect(await connectEdge('snaq://graph/missing.sl', 'snaq://graph/n1.sl', 'x')).toBe(false)
      expect(mockSendRequest).not.toHaveBeenCalled()
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
      mockSendRequest.mockRejectedValue('Server unavailable')
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      const result = await connectEdge('snaq://graph/n1.sl', 'snaq://graph/n2.sl', 'x')

      expect(result).toBe(false)
      expect(useGraphStore.getState().edges).toHaveLength(0)
      expect(addToast).toHaveBeenCalledWith('Server unavailable', 'error')
    })
  })

  describe('disconnectEdge', () => {
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
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputName: 'x',
      })
      mockSendRequest.mockResolvedValue(undefined)

      await disconnectEdge('snaq://graph/n2.sl', 'x')

      expect(mockSendRequest).toHaveBeenCalledTimes(1)
      expect(mockSendRequest).toHaveBeenCalledWith(LSP_METHOD_GRAPH_DISCONNECT, {
        targetUri: 'snaq://graph/n2.sl',
        targetInputName: 'x',
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
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputName: 'x',
      })
      mockSendRequest.mockRejectedValue(new Error('LSP disconnect failed'))
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      await disconnectEdge('snaq://graph/n2.sl', 'x')

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(useGraphStore.getState().edges[0]).toEqual({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputName: 'x',
      })
      expect(addToast).toHaveBeenCalledWith('LSP disconnect failed', 'error')
    })

    it('does nothing when target node not in store', async () => {
      await disconnectEdge('snaq://graph/missing.sl', 'x')
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
      useGraphStore.getState().addEdge({
        sourceId: 'n1',
        targetId: 'n2',
        targetInputName: 'x',
      })
      mockSendRequest.mockRejectedValue('Network error')
      const addToast = vi.fn()
      useUIStore.setState({ addToast })

      await disconnectEdge('snaq://graph/n2.sl', 'x')

      expect(useGraphStore.getState().edges).toHaveLength(1)
      expect(addToast).toHaveBeenCalledWith('Network error', 'error')
    })
  })
})
