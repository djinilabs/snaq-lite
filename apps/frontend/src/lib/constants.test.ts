import { describe, it, expect } from 'vitest'
import {
  VIRTUAL_URI_PREFIX,
  WORKER_MSG_INIT,
  WORKER_MSG_READY,
  WORKER_MSG_ERROR,
  LSP_METHOD_GRAPH_CONNECT,
  LSP_METHOD_GRAPH_DISCONNECT,
  LSP_METHOD_SUBSCRIBE_WIDGET,
  LSP_METHOD_UNSUBSCRIBE_WIDGET,
  LSP_SUBSCRIBE_RETRY_INTERVAL_MS,
  LSP_SUBSCRIBE_MAX_WAIT_MS,
  DRAG_HANDLE_CLASS_COMPUTATION,
  DRAG_HANDLE_CLASS_PRESENTATION,
  NODRAG_CLASS,
  INPUT_PORT_TYPES,
} from './constants'

describe('constants', () => {
  it('worker control message types match protocol', () => {
    expect(WORKER_MSG_INIT).toBe('init')
    expect(WORKER_MSG_READY).toBe('snaqlite-worker-ready')
    expect(WORKER_MSG_ERROR).toBe('snaqlite-worker-error')
  })

  it('VIRTUAL_URI_PREFIX is non-empty and ends with slash', () => {
    expect(VIRTUAL_URI_PREFIX).toBe('snaq://graph/')
    expect(VIRTUAL_URI_PREFIX.length).toBeGreaterThan(0)
  })

  it('LSP graph/widget method names are non-empty strings', () => {
    expect(LSP_METHOD_GRAPH_CONNECT).toBe('snaqlite/graph/connect')
    expect(LSP_METHOD_GRAPH_DISCONNECT).toBe('snaqlite/graph/disconnect')
    expect(LSP_METHOD_SUBSCRIBE_WIDGET).toBe('snaqlite/graph/subscribeWidget')
    expect(LSP_METHOD_UNSUBSCRIBE_WIDGET).toBe('snaqlite/graph/unsubscribeWidget')
  })

  it('LSP subscribe retry and drag handle constants are positive/non-empty', () => {
    expect(LSP_SUBSCRIBE_RETRY_INTERVAL_MS).toBe(200)
    expect(LSP_SUBSCRIBE_MAX_WAIT_MS).toBe(10_000)
    expect(DRAG_HANDLE_CLASS_COMPUTATION).toBe('computation-drag-handle')
    expect(DRAG_HANDLE_CLASS_PRESENTATION).toBe('presentation-drag-handle')
  })

  it('NODRAG_CLASS is non-empty', () => {
    expect(NODRAG_CLASS).toBe('nodrag')
  })

  it('INPUT_PORT_TYPES includes Vector and Numeric', () => {
    expect(INPUT_PORT_TYPES).toContain('Vector')
    expect(INPUT_PORT_TYPES).toContain('Numeric')
    expect(INPUT_PORT_TYPES.length).toBeGreaterThan(0)
  })
})
