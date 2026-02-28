import { describe, it, expect } from 'vitest'
import {
  VIRTUAL_URI_PREFIX,
  LSP_METHOD_GRAPH_CONNECT,
  LSP_METHOD_GRAPH_DISCONNECT,
  LSP_METHOD_SUBSCRIBE_WIDGET,
  LSP_METHOD_UNSUBSCRIBE_WIDGET,
} from './constants'

describe('constants', () => {
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
})
