import { describe, expect, it, vi } from 'vitest'
import type { LspClient } from './client'
import {
  connectCanvasNodes,
  disconnectCanvasNodeInput,
  openCanvasNodes,
  patchCanvasNodeSource,
  toCanvasUri,
} from './canvas-runtime'

function createClientMock(): LspClient {
  return {
    initialize: vi.fn(async () => undefined),
    onNotification: vi.fn(),
    sendRequest: vi.fn(),
    sendNotification: vi.fn(),
    didOpen: vi.fn(async () => undefined),
    didChange: vi.fn(async () => undefined),
    didClose: vi.fn(async () => undefined),
    subscribeNode: vi.fn(async () => ({ subscriptionId: 'sub-1', resultHandle: 'h1' })),
    unsubscribeNode: vi.fn(async () => undefined),
    bootstrapSession: vi.fn(),
    applyPatch: vi.fn(async () => ({ appliedOperations: 1, affectedUris: [] })),
    fetchResultSlice: vi.fn(),
    close: vi.fn(),
  }
}

describe('canvas runtime helpers', () => {
  it('maps URIs to target canvas host', () => {
    expect(toCanvasUri('snaq://canvas-a/node-1.sl', 'canvas-b')).toBe('snaq://canvas-b/node-1.sl')
  })

  it('rejects non-snaq URIs for canvas mapping', () => {
    expect(() => toCanvasUri('file:///tmp/node-1.sl', 'canvas-b')).toThrow(
      'Expected snaq:// URI',
    )
  })

  it('rejects empty canvas id for canvas mapping', () => {
    expect(() => toCanvasUri('snaq://canvas-a/node-1.sl', '   ')).toThrow(
      'canvasId must not be empty',
    )
  })

  it('opens all nodes as deterministic didOpen payloads', async () => {
    const client = createClientMock()
    await openCanvasNodes(
      client,
      [
        { uri: 'snaq://canvas-a/node-1.sl', source: '42', params: [] },
        {
          uri: 'snaq://canvas-a/node-2.sl',
          source: '$x',
          params: [{ name: 'x', paramId: 'p1', typeName: 'Vector' }],
        },
      ],
      'canvas-z',
    )

    expect(client.didOpen).toHaveBeenNthCalledWith(1, {
      uri: 'snaq://canvas-z/node-1.sl',
      text: '42',
      version: 1,
    })
    expect(client.didOpen).toHaveBeenNthCalledWith(2, {
      uri: 'snaq://canvas-z/node-2.sl',
      text: 'input x@p1: Vector\n$x',
      version: 1,
    })
  })

  it('uses applyPatch for node source and edge changes', async () => {
    const client = createClientMock()
    await patchCanvasNodeSource(
      client,
      {
        uri: 'snaq://canvas-a/node-2.sl',
        source: '$x + 1',
        params: [{ name: 'x', paramId: 'p1', typeName: 'Vector' }],
      },
      'canvas-a',
    )
    await connectCanvasNodes(client, {
      sourceUri: 'snaq://canvas-a/node-1.sl',
      targetUri: 'snaq://canvas-a/node-2.sl',
      targetParamId: 'p1',
    })
    await disconnectCanvasNodeInput(client, {
      targetUri: 'snaq://canvas-a/node-2.sl',
      targetParamId: 'p1',
    })

    expect(client.applyPatch).toHaveBeenNthCalledWith(1, [
      {
        op: 'setNodeSource',
        uri: 'snaq://canvas-a/node-2.sl',
        source: 'input x@p1: Vector\n$x + 1',
      },
    ])
    expect(client.applyPatch).toHaveBeenNthCalledWith(2, [
      {
        op: 'connect',
        sourceUri: 'snaq://canvas-a/node-1.sl',
        targetUri: 'snaq://canvas-a/node-2.sl',
        targetInputName: 'p1',
      },
    ])
    expect(client.applyPatch).toHaveBeenNthCalledWith(3, [
      {
        op: 'disconnect',
        targetUri: 'snaq://canvas-a/node-2.sl',
        targetInputName: 'p1',
      },
    ])
  })
})
