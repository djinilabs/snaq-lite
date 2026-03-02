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
  LSP_METHOD_DID_OPEN,
  LSP_METHOD_DID_CHANGE,
  LSP_SUBSCRIBE_RETRY_INTERVAL_MS,
  LSP_SUBSCRIBE_MAX_WAIT_MS,
  DRAG_HANDLE_CLASS_COMPUTATION,
  DRAG_HANDLE_CLASS_PRESENTATION,
  NODRAG_CLASS,
  NOWHEEL_CLASS,
  INPUT_PORT_TYPES,
  AUTO_SAVE_DEBOUNCE_MS,
  UNDO_STACK_MAX,
  DEFAULT_PRESENTATION_DOCUMENT_CONTENT,
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
    expect(LSP_METHOD_DID_OPEN).toBe('textDocument/didOpen')
    expect(LSP_METHOD_DID_CHANGE).toBe('textDocument/didChange')
  })

  it('LSP subscribe retry and drag handle constants are positive/non-empty', () => {
    expect(LSP_SUBSCRIBE_RETRY_INTERVAL_MS).toBe(200)
    expect(LSP_SUBSCRIBE_MAX_WAIT_MS).toBe(10_000)
    expect(DRAG_HANDLE_CLASS_COMPUTATION).toBe('computation-drag-handle')
    expect(DRAG_HANDLE_CLASS_PRESENTATION).toBe('presentation-drag-handle')
  })

  it('NODRAG_CLASS and NOWHEEL_CLASS are non-empty', () => {
    expect(NODRAG_CLASS).toBe('nodrag')
    expect(NOWHEEL_CLASS).toBe('nowheel')
  })

  it('INPUT_PORT_TYPES includes Vector and Numeric', () => {
    expect(INPUT_PORT_TYPES).toContain('Vector')
    expect(INPUT_PORT_TYPES).toContain('Numeric')
    expect(INPUT_PORT_TYPES.length).toBeGreaterThan(0)
  })

  it('AUTO_SAVE_DEBOUNCE_MS and UNDO_STACK_MAX are positive', () => {
    expect(AUTO_SAVE_DEBOUNCE_MS).toBe(600)
    expect(UNDO_STACK_MAX).toBe(10)
  })

  it('DEFAULT_PRESENTATION_DOCUMENT_CONTENT declares input x as Undefined (accept any)', () => {
    expect(DEFAULT_PRESENTATION_DOCUMENT_CONTENT).toContain('input x: Undefined')
    expect(DEFAULT_PRESENTATION_DOCUMENT_CONTENT).toContain('$x')
  })
})
