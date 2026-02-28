import { describe, it, expect, vi } from 'vitest'
import { createLspConnection } from './lsp-connection'

describe('lsp-connection', () => {
  describe('createLspConnection', () => {
    it('returns connection and push function', () => {
      const send = vi.fn()
      const result = createLspConnection(send)
      expect(result).toHaveProperty('connection')
      expect(result).toHaveProperty('push')
      expect(typeof result.push).toBe('function')
    })

    it('writer sends stringified message when connection writes', async () => {
      const send = vi.fn()
      const { connection } = createLspConnection(send)
      connection.listen()
      await connection.sendNotification('test/notification', { key: 'value' })
      expect(send).toHaveBeenCalledTimes(1)
      const raw = send.mock.calls[0][0]
      expect(raw).toContain('"method":"test/notification"')
      expect(raw).toContain('"params":{"key":"value"}')
    })

    it('push delivers notification to connection after listen', async () => {
      const send = vi.fn()
      const { connection, push } = createLspConnection(send)
      const handler = vi.fn()
      connection.onNotification('textDocument/publishDiagnostics', handler)
      connection.listen()
      push(
        JSON.stringify({
          jsonrpc: '2.0',
          method: 'textDocument/publishDiagnostics',
          params: { uri: 'snaq://graph/n1.sl', diagnostics: [{ range: { start: { line: 0, character: 0 }, end: { line: 0, character: 5 } }, message: 'err', severity: 1 }] },
        }),
      )
      await new Promise((r) => setTimeout(r, 0))
      expect(handler).toHaveBeenCalledTimes(1)
      expect(handler).toHaveBeenCalledWith(
        expect.objectContaining({
          uri: 'snaq://graph/n1.sl',
          diagnostics: expect.any(Array),
        }),
      )
    })

    it('push with invalid JSON does not throw', () => {
      const send = vi.fn()
      const { push } = createLspConnection(send)
      expect(() => push('not json')).not.toThrow()
    })

    it('push with invalid JSON does not call listener', async () => {
      const send = vi.fn()
      const { connection, push } = createLspConnection(send)
      const handler = vi.fn()
      connection.onNotification('textDocument/publishDiagnostics', handler)
      connection.listen()
      push('not json')
      await new Promise((r) => setTimeout(r, 0))
      expect(handler).not.toHaveBeenCalled()
    })
  })
})
