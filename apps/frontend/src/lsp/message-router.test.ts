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
  sendFeedStreamFromUrl,
  sendFeedStreamFromReadableStream,
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

    it('handles concatenated plain JSON + Content-Length frame without parse error', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const first = JSON.stringify({ jsonrpc: '2.0', method: 'first', params: {} })
      const second = JSON.stringify({ jsonrpc: '2.0', method: 'second', params: {} })
      const framed = `Content-Length: ${second.length}\r\n\r\n${second}`
      const raw = first + framed
      expect(() => processIncomingMessage(raw)).not.toThrow()
      expect(push).toHaveBeenCalledTimes(2)
      expect(push).toHaveBeenNthCalledWith(1, first)
      expect(push).toHaveBeenNthCalledWith(2, second)
      setIncomingLspPush(null)
    })

    it('handles single Content-Length frame', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const body = JSON.stringify({ jsonrpc: '2.0', method: 'diagnostics', params: {} })
      const raw = `Content-Length: ${body.length}\r\n\r\n${body}`
      expect(() => processIncomingMessage(raw)).not.toThrow()
      expect(push).toHaveBeenCalledTimes(1)
      expect(push).toHaveBeenCalledWith(body)
      setIncomingLspPush(null)
    })

    it('handles two Content-Length frames in one message', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const a = JSON.stringify({ jsonrpc: '2.0', method: 'a', params: {} })
      const b = JSON.stringify({ jsonrpc: '2.0', method: 'b', params: {} })
      const raw = `Content-Length: ${a.length}\r\n\r\n${a}Content-Length: ${b.length}\r\n\r\n${b}`
      expect(() => processIncomingMessage(raw)).not.toThrow()
      expect(push).toHaveBeenCalledTimes(2)
      expect(push).toHaveBeenNthCalledWith(1, a)
      expect(push).toHaveBeenNthCalledWith(2, b)
      setIncomingLspPush(null)
    })

    it('handles plain JSON + two Content-Length frames (three messages)', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const first = JSON.stringify({ jsonrpc: '2.0', method: 'first', params: {} })
      const second = JSON.stringify({ jsonrpc: '2.0', method: 'second', params: {} })
      const third = JSON.stringify({ jsonrpc: '2.0', method: 'third', params: {} })
      const framed2 = `Content-Length: ${second.length}\r\n\r\n${second}`
      const framed3 = `Content-Length: ${third.length}\r\n\r\n${third}`
      const raw = first + framed2 + framed3
      expect(() => processIncomingMessage(raw)).not.toThrow()
      expect(push).toHaveBeenCalledTimes(3)
      expect(push).toHaveBeenNthCalledWith(1, first)
      expect(push).toHaveBeenNthCalledWith(2, second)
      expect(push).toHaveBeenNthCalledWith(3, third)
      setIncomingLspPush(null)
    })

    it('handles Content-Length frames with \\n only (no \\r)', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const a = JSON.stringify({ jsonrpc: '2.0', method: 'a', params: {} })
      const b = JSON.stringify({ jsonrpc: '2.0', method: 'b', params: {} })
      const raw = `Content-Length: ${a.length}\n\n${a}Content-Length: ${b.length}\n\n${b}`
      expect(() => processIncomingMessage(raw)).not.toThrow()
      expect(push).toHaveBeenCalledTimes(2)
      expect(push).toHaveBeenNthCalledWith(1, a)
      expect(push).toHaveBeenNthCalledWith(2, b)
      setIncomingLspPush(null)
    })

    it('handles single frame with concatenated JSON body (split at parse position)', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      const first = JSON.stringify({ jsonrpc: '2.0', method: 'first', params: {} })
      const second = JSON.stringify({ jsonrpc: '2.0', method: 'second', params: {} })
      const body = first + second
      const raw = `Content-Length: ${body.length}\r\n\r\n${body}`
      expect(() => processIncomingMessage(raw)).not.toThrow()
      expect(push).toHaveBeenCalledTimes(2)
      expect(push).toHaveBeenNthCalledWith(1, first)
      expect(push).toHaveBeenNthCalledWith(2, second)
      setIncomingLspPush(null)
    })

    it('empty or whitespace-only input does not throw and does not call push', () => {
      const push = vi.fn()
      setIncomingLspPush(push)
      expect(() => processIncomingMessage('')).not.toThrow()
      expect(push).not.toHaveBeenCalled()
      expect(() => processIncomingMessage('  \n  \r\n  ')).not.toThrow()
      expect(push).not.toHaveBeenCalled()
      setIncomingLspPush(null)
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

  describe('sendFeedStreamFromUrl', () => {
    it('sends JSON message with type, streamIndex, url', () => {
      const messages: string[] = []
      const mockWorker = { postMessage: (msg: string) => messages.push(msg) }
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        sendFeedStreamFromUrl(0, 'https://example.com/data.txt')
        expect(messages).toHaveLength(1)
        const parsed = JSON.parse(messages[0]) as { type: string; streamIndex: number; url: string }
        expect(parsed.type).toBe('feedStreamFromUrl')
        expect(parsed.streamIndex).toBe(0)
        expect(parsed.url).toBe('https://example.com/data.txt')
      } finally {
        setWorkerForTest(null)
      }
    })

    it('includes format in message when provided', () => {
      const messages: string[] = []
      const mockWorker = { postMessage: (msg: string) => messages.push(msg) }
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        sendFeedStreamFromUrl(1, 'https://example.com/data.csv', 'csv')
        expect(messages).toHaveLength(1)
        const parsed = JSON.parse(messages[0]) as {
          type: string
          streamIndex: number
          url: string
          format?: string
        }
        expect(parsed.format).toBe('csv')
        sendFeedStreamFromUrl(2, 'https://x.com/nums.txt', 'numeric')
        const parsed2 = JSON.parse(messages[1]) as { format?: string }
        expect(parsed2.format).toBe('numeric')
      } finally {
        setWorkerForTest(null)
      }
    })

    it('does not include format key when omitted', () => {
      const messages: string[] = []
      const mockWorker = { postMessage: (msg: string) => messages.push(msg) }
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        sendFeedStreamFromUrl(0, 'https://example.com/data.txt')
        const parsed = JSON.parse(messages[0]) as { format?: string }
        expect(parsed).not.toHaveProperty('format')
      } finally {
        setWorkerForTest(null)
      }
    })

    it('does not throw when worker is null (no-op)', () => {
      setWorkerForTest(null)
      expect(() => sendFeedStreamFromUrl(0, 'https://example.com/data.txt')).not.toThrow()
    })
  })

  describe('sendFeedStreamFromReadableStream', () => {
    it('sends object message with type, streamIndex, stream and transfer list', () => {
      const messages: unknown[] = []
      const transferList: unknown[] = []
      const mockWorker = {
        postMessage: (msg: unknown, transfer?: unknown[]) => {
          messages.push(msg)
          if (transfer) transferList.push(...transfer)
        },
      }
      const stream = new ReadableStream()
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        sendFeedStreamFromReadableStream(0, stream)
        expect(messages).toHaveLength(1)
        const payload = messages[0] as { type: string; streamIndex: number; stream: ReadableStream }
        expect(payload.type).toBe('feedStreamFromReadableStream')
        expect(payload.streamIndex).toBe(0)
        expect(payload.stream).toBe(stream)
        expect(transferList).toContain(stream)
      } finally {
        setWorkerForTest(null)
      }
    })

    it('includes format in message when provided', () => {
      const messages: unknown[] = []
      const mockWorker = { postMessage: (msg: unknown) => messages.push(msg) }
      const stream = new ReadableStream()
      setWorkerForTest(mockWorker as unknown as Worker)
      try {
        sendFeedStreamFromReadableStream(0, stream, 'csv')
        const payload = messages[0] as { format?: string }
        expect(payload.format).toBe('csv')
      } finally {
        setWorkerForTest(null)
      }
    })

    it('does not throw when worker is null (no-op)', () => {
      setWorkerForTest(null)
      const stream = new ReadableStream()
      expect(() => sendFeedStreamFromReadableStream(0, stream)).not.toThrow()
    })
  })
})
