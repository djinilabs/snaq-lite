/**
 * Singleton message router: holds Web Worker reference, sends JSON-RPC to worker,
 * routes worker messages (LSP responses and custom notifications) to store and client.
 */

import { routeMessage } from './route-message'

let worker: Worker | null = null
let workerReady = false

export function getWorker(): Worker | null {
  return worker
}

export function isWorkerReady(): boolean {
  return workerReady
}

export function initMessageRouter(workerUrl: URL): void {
  if (worker) return
  worker = new Worker(workerUrl, { type: 'module' })
  worker.onmessage = (event: MessageEvent<string>) => {
    if (typeof event.data === 'string') {
      routeMessage(event.data)
    }
  }
  worker.onerror = (e) => {
    console.error('[LSP Worker]', e)
  }
  workerReady = true
}

export function sendToWorker(message: string): void {
  if (!worker) {
    console.warn('[LSP] Worker not initialized')
    return
  }
  worker.postMessage(message)
}

export function sendRequest(method: string, params?: unknown, id?: string | number): void {
  const msg = {
    jsonrpc: '2.0' as const,
    id: id ?? Math.random().toString(36).slice(2),
    method,
    params,
  }
  sendToWorker(JSON.stringify(msg))
}

export function sendNotification(method: string, params?: unknown): void {
  const msg = {
    jsonrpc: '2.0' as const,
    method,
    params,
  }
  sendToWorker(JSON.stringify(msg))
}
