import { describe, expect, it, vi } from 'vitest'
import { ensureCanvasSession } from './session-orchestrator'
import type { LspClient } from './client'

const makeSendRequest = (impl?: (method: string, params?: unknown) => Promise<unknown>) =>
  (async <TResult = unknown>(method: string, params?: unknown) =>
    ((impl ? await impl(method, params) : {}) as TResult))

function createClientMock(overrides?: Partial<LspClient>): LspClient {
  return {
    initialize: vi.fn(async () => undefined),
    onNotification: vi.fn(),
    sendRequest: makeSendRequest(),
    sendNotification: vi.fn(),
    didOpen: vi.fn(async () => undefined),
    didChange: vi.fn(async () => undefined),
    didClose: vi.fn(async () => undefined),
    subscribeNode: vi.fn(async () => ({ subscriptionId: 'sub-1', resultHandle: 'h1' })),
    unsubscribeNode: vi.fn(async () => undefined),
    bootstrapSession: vi.fn(async () => ({
      canvasId: 'canvas-a',
      openDocuments: 0,
      subscriptions: 0,
      widgets: 0,
      resultHandles: 0,
      runtimeDrained: true,
    })),
    applyPatch: vi.fn(),
    fetchResultSlice: vi.fn(),
    close: vi.fn(),
    ...overrides,
  }
}

describe('ensureCanvasSession', () => {
  it('imports snapshot when already on same canvas', async () => {
    const sendRequestSpy = vi.fn(async () => ({}))
    const client = createClientMock({
      bootstrapSession: vi.fn(async () => ({
        canvasId: 'canvas-a',
        openDocuments: 1,
        subscriptions: 1,
        widgets: 0,
        resultHandles: 1,
        runtimeDrained: false,
      })),
      sendRequest: makeSendRequest(sendRequestSpy),
    })

    await ensureCanvasSession(client, 'canvas-a', {
      canvasId: 'canvas-a',
      nodes: [],
      edges: [],
    })

    expect(sendRequestSpy).toHaveBeenCalledWith('snaqlite/graph/importCanvasDocument', {
      canvasDocument: { canvasId: 'canvas-a', nodes: [], edges: [] },
    })
  })

  it('resets namespace before switching to a different canvas when not drained', async () => {
    const sendRequestSpy = vi.fn(async () => ({}))
    const bootstrapSession = vi
      .fn()
      .mockResolvedValueOnce({
        canvasId: 'canvas-a',
        openDocuments: 2,
        subscriptions: 1,
        widgets: 0,
        resultHandles: 1,
        runtimeDrained: false,
      })
      .mockResolvedValueOnce({
        canvasId: 'canvas-b',
        openDocuments: 0,
        subscriptions: 0,
        widgets: 0,
        resultHandles: 0,
        runtimeDrained: true,
      })
    const client = createClientMock({
      bootstrapSession,
      sendRequest: makeSendRequest(sendRequestSpy),
    })

    await ensureCanvasSession(client, 'canvas-b')

    expect(sendRequestSpy).toHaveBeenCalledWith('snaqlite/graph/resetNamespace', {
      uriPrefix: 'snaq://canvas-a/',
    })
  })
})
