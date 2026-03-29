import { describe, expect, it } from 'vitest'
import { decodeFrames, encodeFrame } from './frame'
import { LspWorkerConnection } from './worker-connection'

class MockWorker {
  onmessage: ((event: MessageEvent<unknown>) => void) | null = null
  readonly sent: unknown[] = []
  terminated = false

  postMessage(message: unknown): void {
    this.sent.push(message)
  }

  emit(message: unknown): void {
    this.onmessage?.({ data: message } as MessageEvent<unknown>)
  }

  terminate(): void {
    this.terminated = true
  }
}

describe('LspWorkerConnection', () => {
  it('handles worker ready and request/response correlation', async () => {
    const worker = new MockWorker()
    const connection = new LspWorkerConnection(() => worker, '/lsp-wasm/snaq_lite_lsp.js')
    worker.emit({ type: 'snaqlite-worker-ready' })
    expect(connection.isReady()).toBe(true)
    await connection.waitUntilReady()

    const promise = connection.request<number>('custom/echo', { n: 10 })
    for (let i = 0; i < 5; i += 1) {
      await Promise.resolve()
    }
    const requestFrame = worker.sent.at(-1)
    expect(typeof requestFrame).toBe('string')
    const parsed = decodeFrames(requestFrame as string).messages[0] as { id: number }
    expect(typeof parsed.id).toBe('number')

    worker.emit(
      encodeFrame({
        jsonrpc: '2.0',
        id: parsed.id,
        result: 10,
      }),
    )

    await expect(promise).resolves.toBe(10)
  })

  it('forwards notifications to listeners', async () => {
    const worker = new MockWorker()
    const connection = new LspWorkerConnection(() => worker, '/lsp-wasm/snaq_lite_lsp.js')
    worker.emit({ type: 'snaqlite-worker-ready' })

    let method = ''
    connection.onNotification((notification) => {
      method = notification.method
    })

    worker.emit(
      encodeFrame({
        jsonrpc: '2.0',
        method: 'snaqlite/publishNodeResult',
        params: { status: 'Completed' },
      }),
    )
    worker.emit(
      encodeFrame({
        jsonrpc: '2.0',
        method: 'snaqlite/graph/widgetDataUpdate',
        params: { status: 'Completed' },
      }),
    )

    expect(method).toBe('snaqlite/graph/widgetDataUpdate')
  })

  it('rejects initialization on worker error', async () => {
    const worker = new MockWorker()
    const connection = new LspWorkerConnection(() => worker, '/lsp-wasm/snaq_lite_lsp.js')
    worker.emit({ type: 'snaqlite-worker-error', error: 'boom' })
    await expect(connection.waitUntilReady()).rejects.toThrow('boom')
  })
})
