/**
 * LSP Web Worker entry. Loads WASM LSP and forwards messages.
 * First message from main must be { type: WORKER_MSG_INIT, wasmUrl: string }.
 * Host stream API: { type: 'createStreamInput', id } → response { type: 'createStreamInputResponse', id, index };
 * { type: 'pushChunk', index, chunk: number[] }; { type: 'closeStream', index }.
 * All other messages are raw LSP JSON-RPC strings, forwarded to push_lsp_message after WASM is ready.
 */

import {
  WORKER_MSG_INIT,
  WORKER_MSG_READY,
  WORKER_MSG_ERROR,
  WORKER_MSG_CREATE_STREAM_RESPONSE,
} from '../lib/constants'

const postMessageCallback = (response: string) => {
  self.postMessage(response)
}

let wasmReady = false
let wasmLoading = false
let pushLspMessageRef: ((s: string) => void) | null = null
let createStreamInputJs: (() => number) | null = null
let pushChunkJs: ((index: number, chunk: number[]) => void) | null = null
let closeStreamJs: ((index: number) => void) | null = null
const buffer: string[] = []

function sendReady(): void {
  self.postMessage(JSON.stringify({ type: WORKER_MSG_READY }))
}

function sendError(error: string): void {
  self.postMessage(JSON.stringify({ type: WORKER_MSG_ERROR, error }))
}

async function loadWasm(wasmUrl: string): Promise<void> {
  if (wasmLoading || wasmReady) return
  wasmLoading = true
  try {
    const mod = await import(/* @vite-ignore */ wasmUrl)
    const init = mod.default
    if (typeof init !== 'function') {
      sendError('WASM module has no default export')
      return
    }
    await init()
    const startSnaqLiteLsp = mod.start_snaq_lite_lsp
    const pushLspMessage = mod.push_lsp_message
    if (typeof startSnaqLiteLsp !== 'function' || typeof pushLspMessage !== 'function') {
      sendError('WASM module missing start_snaq_lite_lsp or push_lsp_message')
      return
    }
    startSnaqLiteLsp(postMessageCallback)
    pushLspMessageRef = pushLspMessage
    createStreamInputJs = typeof mod.create_stream_input_js === 'function' ? mod.create_stream_input_js : null
    pushChunkJs = typeof mod.push_chunk_js === 'function' ? mod.push_chunk_js : null
    closeStreamJs = typeof mod.close_stream_js === 'function' ? mod.close_stream_js : null
    wasmReady = true
    sendReady()
    for (const s of buffer) {
      pushLspMessageRef(s)
    }
    buffer.length = 0
  } catch (err) {
    const message = err instanceof Error ? err.message : String(err)
    sendError(message)
  } finally {
    wasmLoading = false
  }
}

function handleStreamHostMessage(parsed: { type?: string; id?: number; index?: number; chunk?: number[] }): boolean {
  if (!parsed || typeof parsed.type !== 'string') return false
  if (parsed.type === 'createStreamInput' && wasmReady && createStreamInputJs) {
    const index = createStreamInputJs()
    self.postMessage(JSON.stringify({ type: WORKER_MSG_CREATE_STREAM_RESPONSE, id: parsed.id, index }))
    return true
  }
  if (parsed.type === 'pushChunk' && typeof parsed.index === 'number' && Array.isArray(parsed.chunk) && pushChunkJs) {
    try {
      pushChunkJs(parsed.index, parsed.chunk)
    } catch {
      // ignore
    }
    return true
  }
  if (parsed.type === 'closeStream' && typeof parsed.index === 'number' && closeStreamJs) {
    try {
      closeStreamJs(parsed.index)
    } catch {
      // ignore
    }
    return true
  }
  return false
}

self.onmessage = (event: MessageEvent<string>) => {
  const data = event.data
  if (typeof data !== 'string') return

  try {
    const parsed = JSON.parse(data) as { type?: string; wasmUrl?: string }
    if (parsed && parsed.type === WORKER_MSG_INIT && typeof parsed.wasmUrl === 'string') {
      loadWasm(parsed.wasmUrl)
      return
    }
    if (handleStreamHostMessage(parsed)) return
  } catch {
    // not init and not host message; treat as LSP message
  }

  if (wasmReady && pushLspMessageRef) {
    pushLspMessageRef(data)
  } else {
    buffer.push(data)
  }
}
