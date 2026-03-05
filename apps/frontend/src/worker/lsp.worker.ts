/**
 * LSP Web Worker entry. Loads WASM LSP and forwards messages.
 * First message from main must be { type: WORKER_MSG_INIT, wasmUrl: string }.
 * Host stream API: { type: 'createStreamInput', id } → response { type: 'createStreamInputResponse', id, index } or { type, id, error }.
 * { type: 'pushChunk', index, chunk: number[] }; { type: 'closeStream', index }.
 * { type: 'feedStreamFromUrl', streamIndex, url } — worker fetches URL and runs startFeeder (back-pressure).
 * { type: 'feedStreamFromReadableStream', streamIndex, stream } — main thread passes stream (transferable).
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
let startFeederJs: ((streamIndex: number, readableStream: ReadableStream) => void) | null = null
let startCsvFeederJs: ((streamIndex: number, readableStream: ReadableStream) => void) | null = null
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
    startFeederJs = typeof mod.start_feeder_js === 'function' ? mod.start_feeder_js : null
    startCsvFeederJs = typeof mod.start_csv_feeder_js === 'function' ? mod.start_csv_feeder_js : null
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

/** Format hint: 'csv' = row-as-map CSV; 'numeric' or omit = newline-delimited numbers. */
type FeedFormat = 'numeric' | 'csv'

function handleStreamHostMessage(parsed: {
  type?: string
  id?: number
  index?: number
  chunk?: number[]
  url?: string
  stream?: ReadableStream
  format?: FeedFormat
}): boolean {
  if (!parsed || typeof parsed.type !== 'string') return false
  if (parsed.type === 'feedStreamFromUrl' && typeof parsed.streamIndex === 'number' && typeof parsed.url === 'string') {
    const format: FeedFormat = parsed.format === 'csv' ? 'csv' : 'numeric'
    const useCsv = format === 'csv' && startCsvFeederJs
    const feeder = useCsv ? startCsvFeederJs : startFeederJs
    if (wasmReady && feeder) {
      const streamIndex = parsed.streamIndex
      const url = parsed.url
      ;(async () => {
        try {
          const res = await fetch(url)
          if (!res.body || !res.ok) return
          feeder(streamIndex, res.body)
        } catch {
          // ignore fetch error
        }
      })()
    }
    return true
  }
  if (
    parsed.type === 'feedStreamFromReadableStream' &&
    typeof parsed.streamIndex === 'number' &&
    parsed.stream instanceof ReadableStream
  ) {
    const format: FeedFormat = parsed.format === 'csv' ? 'csv' : 'numeric'
    const useCsv = format === 'csv' && startCsvFeederJs
    const feeder = useCsv ? startCsvFeederJs : startFeederJs
    if (wasmReady && feeder) {
      try {
        feeder(parsed.streamIndex, parsed.stream)
      } catch {
        // ignore
      }
    }
    return true
  }
  if (parsed.type === 'createStreamInput') {
    if (wasmReady && createStreamInputJs) {
      try {
        const index = createStreamInputJs()
        self.postMessage(JSON.stringify({ type: WORKER_MSG_CREATE_STREAM_RESPONSE, id: parsed.id, index }))
      } catch (err) {
        const message = err instanceof Error ? err.message : String(err)
        self.postMessage(JSON.stringify({ type: WORKER_MSG_CREATE_STREAM_RESPONSE, id: parsed.id, error: message }))
      }
    } else {
      self.postMessage(
        JSON.stringify({
          type: WORKER_MSG_CREATE_STREAM_RESPONSE,
          id: parsed.id,
          error: 'Worker or stream host not ready',
        }),
      )
    }
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

self.onmessage = (event: MessageEvent<string | { type?: string; wasmUrl?: string; streamIndex?: number; url?: string; stream?: ReadableStream }>) => {
  const data = event.data
  if (typeof data === 'object' && data !== null) {
    if (data.type === WORKER_MSG_INIT && typeof data.wasmUrl === 'string') {
      loadWasm(data.wasmUrl)
      return
    }
    if (handleStreamHostMessage(data)) return
    return
  }
  if (typeof data !== 'string') return

  try {
    const parsed = JSON.parse(data) as { type?: string; wasmUrl?: string; streamIndex?: number; url?: string }
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
