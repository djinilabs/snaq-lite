import { describe, it, expect, beforeEach, vi } from 'vitest'
import {
  WORKER_MSG_READY,
  WORKER_MSG_ERROR,
  WORKER_MSG_CREATE_STREAM_RESPONSE,
} from '~/lib/constants'
import {
  processIncomingWorkerMessage,
  processIncomingMessage,
  isWorkerReady,
  waitForWorkerReady,
  setIncomingLspPush,
  resetMessageRouterForTest,
  setWorkerForTest,
  requestCreateStreamInput,
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

  describe('createStreamInputResponse', () => {
    it('processIncomingWorkerMessage returns true for createStreamInputResponse with index', () => {
      const raw = JSON.stringify({
        type: WORKER_MSG_CREATE_STREAM_RESPONSE,
        id: 0,
        index: 0,
      })
      const got = processIncomingWorkerMessage(raw)
      expect(got).toBe(true)
    })

    it('processIncomingWorkerMessage returns true for createStreamInputResponse with error', () => {
      const raw = JSON.stringify({
        type: WORKER_MSG_CREATE_STREAM_RESPONSE,
        id: 0,
        error: 'Worker or stream host not ready',
      })
      const got = processIncomingWorkerMessage(raw)
      expect(got).toBe(true)
    })

    it('requestCreateStreamInput resolves when worker responds with index', async () => {
      const messages: string[] = []
      const mockWorker = {
        postMessage(msg: string) {
          messages.push(msg)
        },
      }
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))

        const promise = requestCreateStreamInput()
        await Promise.resolve()
        expect(messages).toHaveLength(1)
        const sent = JSON.parse(messages[0]) as { type: string; id: number }
        expect(sent.type).toBe('createStreamInput')
        expect(typeof sent.id).toBe('number')
        const id = sent.id

        processIncomingMessage(
          JSON.stringify({
            type: WORKER_MSG_CREATE_STREAM_RESPONSE,
            id,
            index: 0,
          }),
        )
        await expect(promise).resolves.toBe(0)
      } finally {
        setWorkerForTest(null)
      }
    })

    it('requestCreateStreamInput rejects when worker responds with error', async () => {
      const messages: string[] = []
      const mockWorker = {
        postMessage(msg: string) {
          messages.push(msg)
        },
      }
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))

        const promise = requestCreateStreamInput()
        await Promise.resolve()
        expect(messages).toHaveLength(1)
        const sent = JSON.parse(messages[0]) as { type: string; id: number }
        const id = sent.id

        processIncomingMessage(
          JSON.stringify({
            type: WORKER_MSG_CREATE_STREAM_RESPONSE,
            id,
            error: 'Worker or stream host not ready',
          }),
        )
        await expect(promise).rejects.toThrow('Worker or stream host not ready')
      } finally {
        setWorkerForTest(null)
      }
    })

    it('resetMessageRouterForTest rejects pending createStreamInput promises', async () => {
      const mockWorker = { postMessage: () => {} }
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        processIncomingWorkerMessage(JSON.stringify({ type: WORKER_MSG_READY }))
        const promise = requestCreateStreamInput()
        await Promise.resolve()
        resetMessageRouterForTest()
        await expect(promise).rejects.toThrow('Message router reset')
      } finally {
        setWorkerForTest(null)
      }
    })
  })
})
