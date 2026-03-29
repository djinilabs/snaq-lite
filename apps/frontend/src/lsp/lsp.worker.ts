/// <reference lib="webworker" />

type WasmExports = {
  default: (moduleOrPath?: string | URL | Response | BufferSource | WebAssembly.Module) => Promise<unknown>
  start_snaq_lite_lsp: (postMessageCallback: (message: string) => void) => void
  push_lsp_message: (message: string) => void
}

let ready = false
let loading = false
let pushMessage: ((message: string) => void) | null = null
const queued: string[] = []

async function handleInit(wasmUrl: string) {
  if (ready || loading) {
    return
  }
  loading = true
  try {
    const mod = (await import(/* @vite-ignore */ wasmUrl)) as WasmExports
    await mod.default()
    mod.start_snaq_lite_lsp((message: string) => self.postMessage(message))
    pushMessage = mod.push_lsp_message
    ready = true
    self.postMessage({ type: 'snaqlite-worker-ready' })
    for (const message of queued.splice(0)) {
      pushMessage(message)
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : 'unknown worker initialization error'
    self.postMessage({ type: 'snaqlite-worker-error', error: message })
  } finally {
    loading = false
  }
}

self.onmessage = (event: MessageEvent<unknown>) => {
  const data = event.data
  if (typeof data === 'object' && data !== null && 'type' in data && (data as { type: string }).type === 'init') {
    const wasmUrl = (data as { wasmUrl?: string }).wasmUrl
    if (!wasmUrl) {
      self.postMessage({ type: 'snaqlite-worker-error', error: 'missing wasmUrl in init message' })
      return
    }
    void handleInit(wasmUrl)
    return
  }
  if (typeof data !== 'string') {
    return
  }
  if (ready && pushMessage) {
    pushMessage(data)
    return
  }
  queued.push(data)
}
