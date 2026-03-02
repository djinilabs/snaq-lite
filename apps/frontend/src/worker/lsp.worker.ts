/**
 * LSP Web Worker entry. Loads WASM LSP and forwards messages.
 * First message from main must be { type: WORKER_MSG_INIT, wasmUrl: string }.
 * All other messages are raw LSP JSON-RPC strings, forwarded to push_lsp_message after WASM is ready.
 */

import { WORKER_MSG_INIT, WORKER_MSG_READY, WORKER_MSG_ERROR } from '../lib/constants'

const postMessageCallback = (response: string) => {
  self.postMessage(response)
}

let wasmReady = false
let wasmLoading = false
let pushLspMessageRef: ((s: string) => void) | null = null
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

self.onmessage = (event: MessageEvent<string>) => {
  const data = event.data
  if (typeof data !== 'string') return

  try {
    const parsed = JSON.parse(data) as { type?: string; wasmUrl?: string }
    if (parsed && parsed.type === WORKER_MSG_INIT && typeof parsed.wasmUrl === 'string') {
      loadWasm(parsed.wasmUrl)
      return
    }
  } catch {
    // not init; treat as LSP message
  }

  if (wasmReady && pushLspMessageRef) {
    pushLspMessageRef(data)
  } else {
    buffer.push(data)
  }
}
