import { beforeEach, describe, expect, it, vi } from 'vitest'
import type { JsonRpcNotification } from './types'

const notifyMock = vi.fn(async () => undefined)
const requestMock = vi.fn(async () => ({}))
const onNotificationMock = vi.fn()
const closeMock = vi.fn()

vi.mock('./worker-connection', () => {
  return {
    LspWorkerConnection: vi.fn().mockImplementation(() => ({
      request: requestMock,
      notify: notifyMock,
      onNotification: onNotificationMock,
      close: closeMock,
    })),
  }
})

import { createLspClient } from './client'

describe('createLspClient document versioning', () => {
  beforeEach(() => {
    notifyMock.mockClear()
    requestMock.mockClear()
    onNotificationMock.mockClear()
    closeMock.mockClear()
  })

  it('increments didChange version monotonically when version is omitted', async () => {
    const client = createLspClient({
      wasmUrl: '/lsp-wasm/snaq_lite_lsp.js',
      workerFactory: () => ({}) as Worker,
    })
    const uri = 'snaq://canvas-a/node-1.sl'

    await client.didOpen({ uri, text: '1' })
    await client.didChange({ uri, text: '2' })
    await client.didChange({ uri, text: '3' })

    expect(notifyMock).toHaveBeenNthCalledWith(1, 'textDocument/didOpen', {
      textDocument: {
        uri,
        languageId: 'snaq',
        version: 1,
        text: '1',
      },
    })
    expect(notifyMock).toHaveBeenNthCalledWith(2, 'textDocument/didChange', {
      textDocument: { uri, version: 2 },
      contentChanges: [{ text: '2' }],
    })
    expect(notifyMock).toHaveBeenNthCalledWith(3, 'textDocument/didChange', {
      textDocument: { uri, version: 3 },
      contentChanges: [{ text: '3' }],
    })
  })

  it('rejects non-increasing didChange versions when explicit version is provided', async () => {
    const client = createLspClient({
      wasmUrl: '/lsp-wasm/snaq_lite_lsp.js',
      workerFactory: () => ({}) as Worker,
    })
    const uri = 'snaq://canvas-a/node-1.sl'

    await client.didOpen({ uri, text: '1', version: 4 })
    await expect(client.didChange({ uri, text: '2', version: 4 })).rejects.toThrow(
      'didChange version must be greater than current version (4)',
    )
    expect(notifyMock).toHaveBeenCalledTimes(1)
  })

  it('resets tracked version on didClose', async () => {
    const client = createLspClient({
      wasmUrl: '/lsp-wasm/snaq_lite_lsp.js',
      workerFactory: () => ({}) as Worker,
    })
    const uri = 'snaq://canvas-a/node-1.sl'

    await client.didOpen({ uri, text: '1' })
    await client.didChange({ uri, text: '2' })
    await client.didClose(uri)
    await client.didChange({ uri, text: '3' })

    expect(notifyMock).toHaveBeenNthCalledWith(4, 'textDocument/didChange', {
      textDocument: { uri, version: 1 },
      contentChanges: [{ text: '3' }],
    })
  })

  it('forwards notification handlers', () => {
    const client = createLspClient({
      wasmUrl: '/lsp-wasm/snaq_lite_lsp.js',
      workerFactory: () => ({}) as Worker,
    })
    const handler = (_notification: JsonRpcNotification): void => undefined
    client.onNotification(handler)
    expect(onNotificationMock).toHaveBeenCalledWith(handler)
  })
})
