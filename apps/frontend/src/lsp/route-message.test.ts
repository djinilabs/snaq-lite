import { describe, it, expect, beforeEach, vi } from 'vitest'
import { routeMessage, setMessageRouterHandlers, clearMessageRouterHandlers } from './route-message'

describe('route-message', () => {
  beforeEach(() => {
    clearMessageRouterHandlers()
  })

  it('ignores invalid JSON', () => {
    const onLspResponse = vi.fn()
    setMessageRouterHandlers({ onLspResponse })
    routeMessage('not json')
    expect(onLspResponse).not.toHaveBeenCalled()
  })

  it('dispatches response to onLspResponse', () => {
    const onLspResponse = vi.fn()
    setMessageRouterHandlers({ onLspResponse })
    routeMessage(JSON.stringify({ jsonrpc: '2.0', id: 42, result: { cap: {} } }))
    expect(onLspResponse).toHaveBeenCalledWith(
      expect.objectContaining({ id: 42, result: { cap: {} } }),
    )
  })

  it('dispatches nodeSignatureUpdated to onNodeSignatureUpdated', () => {
    const onNodeSignatureUpdated = vi.fn()
    setMessageRouterHandlers({ onNodeSignatureUpdated })
    const params = { uri: 'snaq://graph/n1.sl', inputs: [{ name: 'x', type: 'Vector' }], outputType: 'Numeric' }
    routeMessage(
      JSON.stringify({
        jsonrpc: '2.0',
        method: 'snaqlite/graph/nodeSignatureUpdated',
        params,
      }),
    )
    expect(onNodeSignatureUpdated).toHaveBeenCalledWith(params)
  })

  it('dispatches widgetDataUpdate to onWidgetDataUpdate', () => {
    const onWidgetDataUpdate = vi.fn()
    setMessageRouterHandlers({ onWidgetDataUpdate })
    const params = { widgetId: 'w1', status: 'Completed' as const, payload: { totalElements: 10 } }
    routeMessage(
      JSON.stringify({
        jsonrpc: '2.0',
        method: 'snaqlite/graph/widgetDataUpdate',
        params,
      }),
    )
    expect(onWidgetDataUpdate).toHaveBeenCalledWith(params)
  })

  it('dispatches publishDiagnostics to onPublishDiagnostics when set', () => {
    const onPublishDiagnostics = vi.fn()
    setMessageRouterHandlers({ onPublishDiagnostics })
    const params = { uri: 'snaq://graph/n1.sl', diagnostics: [{ range: { start: { line: 0, character: 0 }, end: { line: 0, character: 5 } }, message: 'parse error', severity: 1 }] }
    routeMessage(
      JSON.stringify({ jsonrpc: '2.0', method: 'textDocument/publishDiagnostics', params }),
    )
    expect(onPublishDiagnostics).toHaveBeenCalledWith(params)
  })

  it('does not call custom handlers for unknown notification', () => {
    const onNodeSignatureUpdated = vi.fn()
    const onWidgetDataUpdate = vi.fn()
    setMessageRouterHandlers({ onNodeSignatureUpdated, onWidgetDataUpdate })
    routeMessage(JSON.stringify({ jsonrpc: '2.0', method: 'other/notification', params: {} }))
    expect(onNodeSignatureUpdated).not.toHaveBeenCalled()
    expect(onWidgetDataUpdate).not.toHaveBeenCalled()
  })
})
