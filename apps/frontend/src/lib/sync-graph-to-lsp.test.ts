import { describe, it, expect, beforeEach, vi } from 'vitest'
import {
  LSP_METHOD_DID_OPEN,
  LSP_METHOD_GRAPH_CONNECT,
  LSP_SUBSCRIBE_AFTER_DID_OPEN_MS,
} from '~/lib/constants'
import { syncLoadedGraphToLsp } from './sync-graph-to-lsp'
import type { GraphEdge, GraphNode } from '~/store'

const mockSendRequest = vi.fn()
const mockSendNotification = vi.fn()
const mockClient = {
  sendRequest: mockSendRequest,
  sendNotification: mockSendNotification,
}

vi.mock('~/lsp/language-client-singleton', () => ({
  waitForLanguageClient: () => Promise.resolve(mockClient),
  getLanguageClient: () => mockClient,
  whenClientReady: () => {},
}))

describe('syncLoadedGraphToLsp', () => {
  beforeEach(() => {
    vi.useFakeTimers()
    mockSendRequest.mockReset()
    mockSendNotification.mockReset()
    mockSendRequest.mockResolvedValue(undefined)
  })

  afterEach(() => {
    vi.useRealTimers()
  })

  it('sends graph/connect with targetInputName derived from target node input at targetInputIndex', async () => {
    const nodes: GraphNode[] = [
      {
        id: 'a',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/a.sl',
        initialContent: '1',
        inputs: [{ name: 'x', type: 'Vector' }],
      },
      {
        id: 'b',
        position: { x: 100, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/b.sl',
        initialContent: '2',
        inputs: [{ name: 'first', type: 'Numeric' }, { name: 'second', type: 'Vector' }],
      },
    ]
    const edges: GraphEdge[] = [
      { sourceId: 'a', targetId: 'b', targetInputIndex: 1 },
    ]

    const syncPromise = syncLoadedGraphToLsp(nodes, edges)
    await vi.advanceTimersByTimeAsync(LSP_SUBSCRIBE_AFTER_DID_OPEN_MS)
    await syncPromise

    expect(mockSendRequest).toHaveBeenCalledTimes(1)
    expect(mockSendRequest).toHaveBeenCalledWith(LSP_METHOD_GRAPH_CONNECT, {
      sourceUri: 'snaq://graph/a.sl',
      targetUri: 'snaq://graph/b.sl',
      targetInputName: 'second',
    })
    expect(mockSendNotification).toHaveBeenCalledTimes(2)
    expect(mockSendNotification).toHaveBeenCalledWith(
      LSP_METHOD_DID_OPEN,
      expect.objectContaining({
        textDocument: expect.objectContaining({ uri: 'snaq://graph/a.sl' }),
      }),
    )
    expect(mockSendNotification).toHaveBeenCalledWith(
      LSP_METHOD_DID_OPEN,
      expect.objectContaining({
        textDocument: expect.objectContaining({ uri: 'snaq://graph/b.sl' }),
      }),
    )
  })

  it('skips edge when target has no input at targetInputIndex', async () => {
    const nodes: GraphNode[] = [
      {
        id: 'a',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/a.sl',
        inputs: [{ name: 'x', type: 'Vector' }],
      },
      {
        id: 'b',
        position: { x: 100, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/b.sl',
        inputs: [{ name: 'only', type: 'Numeric' }],
      },
    ]
    const edges: GraphEdge[] = [
      { sourceId: 'a', targetId: 'b', targetInputIndex: 5 },
    ]

    const syncPromise = syncLoadedGraphToLsp(nodes, edges)
    await vi.advanceTimersByTimeAsync(LSP_SUBSCRIBE_AFTER_DID_OPEN_MS)
    await syncPromise

    expect(mockSendRequest).not.toHaveBeenCalled()
  })

  it('skips edge when target input at index has empty or whitespace name', async () => {
    const nodes: GraphNode[] = [
      {
        id: 'a',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/a.sl',
        inputs: [{ name: 'x', type: 'Vector' }],
      },
      {
        id: 'b',
        position: { x: 100, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/b.sl',
        inputs: [{ name: '  ', type: 'Numeric' }],
      },
    ]
    const edges: GraphEdge[] = [
      { sourceId: 'a', targetId: 'b', targetInputIndex: 0 },
    ]

    const syncPromise = syncLoadedGraphToLsp(nodes, edges)
    await vi.advanceTimersByTimeAsync(LSP_SUBSCRIBE_AFTER_DID_OPEN_MS)
    await syncPromise

    expect(mockSendRequest).not.toHaveBeenCalled()
  })

  it('does not send didOpen for file nodes and skips graph/connect for edges whose source is file', async () => {
    const nodes: GraphNode[] = [
      {
        id: 'file1',
        position: { x: 0, y: 0 },
        type: 'file',
        uri: 'snaq://graph/file1.sl',
        url: 'blob:xxx',
      },
      {
        id: 'n2',
        position: { x: 100, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/n2.sl',
        inputs: [{ name: 'data', type: 'Vector' }],
      },
    ]
    const edges: GraphEdge[] = [
      { sourceId: 'file1', targetId: 'n2', targetInputIndex: 0 },
    ]

    const syncPromise = syncLoadedGraphToLsp(nodes, edges)
    await vi.advanceTimersByTimeAsync(LSP_SUBSCRIBE_AFTER_DID_OPEN_MS)
    await syncPromise

    expect(mockSendRequest).not.toHaveBeenCalled()
    expect(mockSendNotification).toHaveBeenCalledTimes(1)
    expect(mockSendNotification).toHaveBeenCalledWith(
      LSP_METHOD_DID_OPEN,
      expect.objectContaining({
        textDocument: expect.objectContaining({ uri: 'snaq://graph/n2.sl' }),
      }),
    )
  })

  it('sends correct targetInputName for each edge when multiple edges target same node at different indices', async () => {
    const nodes: GraphNode[] = [
      {
        id: 'src1',
        position: { x: 0, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/src1.sl',
        inputs: [],
      },
      {
        id: 'src2',
        position: { x: 0, y: 50 },
        type: 'computation',
        uri: 'snaq://graph/src2.sl',
        inputs: [],
      },
      {
        id: 'tgt',
        position: { x: 200, y: 0 },
        type: 'computation',
        uri: 'snaq://graph/tgt.sl',
        inputs: [
          { name: 'alpha', type: 'Numeric' },
          { name: 'beta', type: 'Vector' },
        ],
      },
    ]
    const edges: GraphEdge[] = [
      { sourceId: 'src1', targetId: 'tgt', targetInputIndex: 0 },
      { sourceId: 'src2', targetId: 'tgt', targetInputIndex: 1 },
    ]

    const syncPromise = syncLoadedGraphToLsp(nodes, edges)
    await vi.advanceTimersByTimeAsync(LSP_SUBSCRIBE_AFTER_DID_OPEN_MS)
    await syncPromise

    expect(mockSendRequest).toHaveBeenCalledTimes(2)
    expect(mockSendRequest).toHaveBeenNthCalledWith(1, LSP_METHOD_GRAPH_CONNECT, {
      sourceUri: 'snaq://graph/src1.sl',
      targetUri: 'snaq://graph/tgt.sl',
      targetInputName: 'alpha',
    })
    expect(mockSendRequest).toHaveBeenNthCalledWith(2, LSP_METHOD_GRAPH_CONNECT, {
      sourceUri: 'snaq://graph/src2.sl',
      targetUri: 'snaq://graph/tgt.sl',
      targetInputName: 'beta',
    })
  })
})
