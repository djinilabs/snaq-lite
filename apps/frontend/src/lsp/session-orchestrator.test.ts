import { describe, expect, it, vi } from 'vitest'
import {
  ensureCanvasSession,
  planEnsureCanvasSessionRequests,
} from './session-orchestrator'
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
      canvasRevision: 0,
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
        canvasRevision: 3,
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
        canvasRevision: 4,
        openDocuments: 2,
        subscriptions: 1,
        widgets: 0,
        resultHandles: 1,
        runtimeDrained: false,
      })
      .mockResolvedValueOnce({
        canvasId: 'canvas-b',
        canvasRevision: 0,
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

describe('planEnsureCanvasSessionRequests', () => {
  const snapshot = {
    canvasId: 'demo',
    revision: 1,
    nodes: [{ uri: 'snaq://demo/a.sl', source: '1 + 1' }],
    edges: [] as { sourceUri: string; targetUri: string; targetParamId: string }[],
  }

  it('plans bootstrap + import when canvas matches or server has no canvas', () => {
    expect(planEnsureCanvasSessionRequests('demo', snapshot, { canvasId: 'demo', runtimeDrained: true })).toEqual([
      { method: 'snaqlite/bootstrapSession', params: {} },
      { method: 'snaqlite/graph/importCanvasDocument', params: { canvasDocument: snapshot } },
    ])
    expect(planEnsureCanvasSessionRequests('demo', snapshot, { canvasId: undefined, runtimeDrained: true })).toEqual([
      { method: 'snaqlite/bootstrapSession', params: {} },
      { method: 'snaqlite/graph/importCanvasDocument', params: { canvasDocument: snapshot } },
    ])
  })

  it('plans resetNamespace + import + second bootstrap when switching canvases with live runtime', () => {
    expect(
      planEnsureCanvasSessionRequests('other', snapshot, { canvasId: 'demo', runtimeDrained: false }),
    ).toEqual([
      { method: 'snaqlite/bootstrapSession', params: {} },
      { method: 'snaqlite/graph/resetNamespace', params: { uriPrefix: 'snaq://demo/' } },
      { method: 'snaqlite/graph/importCanvasDocument', params: { canvasDocument: snapshot } },
      { method: 'snaqlite/bootstrapSession', params: {} },
    ])
  })

  it('skips resetNamespace when runtime is already drained', () => {
    expect(
      planEnsureCanvasSessionRequests('other', snapshot, { canvasId: 'demo', runtimeDrained: true }),
    ).toEqual([
      { method: 'snaqlite/bootstrapSession', params: {} },
      { method: 'snaqlite/graph/importCanvasDocument', params: { canvasDocument: snapshot } },
      { method: 'snaqlite/bootstrapSession', params: {} },
    ])
  })
})
