import { describe, it, expect, beforeEach, vi } from 'vitest'
import { WORKER_MSG_READY, WORKER_MSG_ERROR } from '~/lib/constants'
import {
  processIncomingWorkerMessage,
  processIncomingMessage,
  isWorkerReady,
  waitForWorkerReady,
  setIncomingLspPush,
  resetMessageRouterForTest,
} from './message-router'

describe('message-router', () => {
  beforeEach(() => {
    resetMessageRouterForTest()
  })

  describe('processIncomingWorkerMessage', () => {
    it('handles snaqlite-worker-ready: returns true and sets workerReady', () => {
      const raw = JSON.stringify({ type: WORKER_MSG_READY })
      const got = processIncomingWorkerMessage(raw)
      expect(got).toBe(true)
      expect(isWorkerReady()).toBe(true)
    })

    it('handles snaqlite-worker-error: returns true and sets workerReady false', () => {
      const consoleError = vi.spyOn(console, 'error').mockImplementation(() => {})
      processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))
      expect(isWorkerReady()).toBe(true)

      const raw = JSON.stringify({ type: WORKER_MSG_ERROR, error: 'load failed' })
      const got = processIncomingWorkerMessage(raw)
      expect(got).toBe(true)
      expect(isWorkerReady()).toBe(false)
      consoleError.mockRestore()
    })

    it('returns false for LSP JSON-RPC response so caller passes to routeMessage', () => {
      resetMessageRouterForTest()
      const lspResponse = JSON.stringify({ jsonrpc: '2.0', id: 1, result: { capabilities: {} } })
      const got = processIncomingWorkerMessage(lspResponse)
      expect(got).toBe(false)
      expect(isWorkerReady()).toBe(false)
    })

    it('returns false for LSP message when worker was already ready', () => {
      processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))
      expect(isWorkerReady()).toBe(true)

      const lspNotification = JSON.stringify({
        jsonrpc: '2.0',
        method: 'textDocument/publishDiagnostics',
        params: {},
      })
      const got = processIncomingWorkerMessage(lspNotification)
      expect(got).toBe(false)
      expect(isWorkerReady()).toBe(true)
    })

    it('returns false for invalid JSON', () => {
      const got = processIncomingWorkerMessage('not json')
      expect(got).toBe(false)
    })

    it('returns false for JSON without type (LSP message)', () => {
      const got = processIncomingWorkerMessage(JSON.stringify({ jsonrpc: '2.0', method: 'foo' }))
      expect(got).toBe(false)
    })
  })

  describe('waitForWorkerReady', () => {
    it('resolves when ready message is processed', async () => {
      const readyPromise = waitForWorkerReady()
      processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))
      await expect(readyPromise).resolves.toBeUndefined()
      expect(isWorkerReady()).toBe(true)
    })

    it('resolves immediately if worker already ready', async () => {
      processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))
      await expect(waitForWorkerReady()).resolves.toBeUndefined()
    })
  })

  describe('setIncomingLspPush and processIncomingMessage', () => {
    it('calls incomingLspPush when processIncomingMessage receives LSP message', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const lspMsg = JSON.stringify({ jsonrpc: '2.0', method: 'textDocument/publishDiagnostics', params: {} })
      processIncomingMessage(lspMsg)
      expect(push).toHaveBeenCalledTimes(1)
      expect(push).toHaveBeenCalledWith(lspMsg)
      setIncomingLspPush(null)
    })

    it('does not call incomingLspPush for control message (ready)', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      processIncomingMessage(JSON.stringify({ type: WORKER_MSG_READY }))
      expect(push).not.toHaveBeenCalled()
      setIncomingLspPush(null)
    })

    it('does not throw when incomingLspPush is null', () => {
      setIncomingLspPush(null)
      expect(() =>
        processIncomingMessage(JSON.stringify({ jsonrpc: '2.0', method: 'foo', params: {} })),
      ).not.toThrow()
    })
  })
})
