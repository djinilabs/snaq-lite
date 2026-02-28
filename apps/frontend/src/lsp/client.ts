/**
 * Initializes the LSP worker. The actual LSP traffic (sendRequest/sendNotification)
 * goes through the language client singleton (getLanguageClient()) after LspProvider
 * starts the connection. Call initLspClient once at app startup.
 */

import { initMessageRouter } from './message-router'

/**
 * Initialize the LSP worker. Call once at app startup (e.g. from LspProvider).
 * When wasmUrl is provided, the worker loads the LSP WASM from that URL; omit for stub/test mode.
 */
export function initLspClient(workerUrl: URL, wasmUrl?: string): void {
  initMessageRouter(workerUrl, wasmUrl)
}
