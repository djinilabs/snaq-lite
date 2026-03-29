import { decodeFrames, encodeFrame } from './frame'
import type {
  JsonRpcFailure,
  JsonRpcId,
  JsonRpcInbound,
  JsonRpcNotification,
  JsonRpcRequest,
  JsonRpcSuccess,
  WorkerControlMessage,
} from './types'

type WorkerLike = {
  postMessage: (message: unknown) => void
  onmessage: ((event: MessageEvent<unknown>) => void) | null
  terminate: () => void
}

type PendingRequest = {
  resolve: (value: unknown) => void
  reject: (reason: Error) => void
}

type WorkerFactory = () => WorkerLike

export type NotificationHandler = (notification: JsonRpcNotification) => void

const WORKER_READY_TIMEOUT_MS = 15_000

export class LspWorkerConnection {
  private readonly worker: WorkerLike
  private readonly pending = new Map<JsonRpcId, PendingRequest>()
  private readonly pendingInit: {
    resolve: () => void
    reject: (reason: Error) => void
    promise: Promise<void>
  }
  private id = 0
  private initialized = false
  private inboundBuffer = ''
  private notificationHandler: NotificationHandler = () => undefined

  constructor(workerFactory: WorkerFactory, wasmUrl: string) {
    this.worker = workerFactory()
    this.pendingInit = this.createInitPromise()
    this.worker.onmessage = (event) => this.handleWorkerMessage(event)
    this.worker.postMessage({ type: 'init', wasmUrl })
  }

  private createInitPromise() {
    let resolveRef: () => void = () => undefined
    let rejectRef: (reason: Error) => void = (_reason: Error) => undefined
    let settled = false
    const timeoutId = setTimeout(() => {
      if (settled) {
        return
      }
      settled = true
      rejectRef(new Error(`LSP worker did not become ready within ${WORKER_READY_TIMEOUT_MS}ms`))
    }, WORKER_READY_TIMEOUT_MS)
    const promise = new Promise<void>((resolve, reject) => {
      resolveRef = () => {
        if (settled) {
          return
        }
        settled = true
        clearTimeout(timeoutId)
        resolve()
      }
      rejectRef = (reason: Error) => {
        if (settled) {
          return
        }
        settled = true
        clearTimeout(timeoutId)
        reject(reason)
      }
    })
    return { resolve: resolveRef, reject: rejectRef, promise }
  }

  async waitUntilReady(): Promise<void> {
    await this.pendingInit.promise
  }

  onNotification(handler: NotificationHandler): void {
    this.notificationHandler = handler
  }

  async request<TResult = unknown>(method: string, params?: unknown): Promise<TResult> {
    await this.waitUntilReady()
    const id = ++this.id
    const message: JsonRpcRequest = {
      jsonrpc: '2.0',
      id,
      method,
      params,
    }
    const response = await new Promise<unknown>((resolve, reject) => {
      this.pending.set(id, { resolve, reject })
      this.worker.postMessage(encodeFrame(message))
    })
    return response as TResult
  }

  async notify(method: string, params?: unknown): Promise<void> {
    await this.waitUntilReady()
    const message: JsonRpcNotification = {
      jsonrpc: '2.0',
      method,
      params,
    }
    this.worker.postMessage(encodeFrame(message))
  }

  close(): void {
    this.worker.terminate()
    for (const pending of this.pending.values()) {
      pending.reject(new Error('LSP worker connection closed'))
    }
    this.pending.clear()
  }

  private handleWorkerMessage(event: MessageEvent<unknown>): void {
    const payload = event.data
    if (typeof payload === 'object' && payload !== null && 'type' in payload) {
      this.handleControlMessage(payload as WorkerControlMessage)
      return
    }
    if (typeof payload !== 'string') {
      return
    }
    this.inboundBuffer += payload
    const { messages, rest } = decodeFrames(this.inboundBuffer)
    this.inboundBuffer = rest
    for (const message of messages) {
      this.routeInboundMessage(message as JsonRpcInbound)
    }
  }

  private handleControlMessage(message: WorkerControlMessage): void {
    if (message.type === 'snaqlite-worker-ready') {
      this.initialized = true
      this.pendingInit.resolve()
      return
    }
    if (message.type === 'snaqlite-worker-error') {
      const err = new Error(message.error)
      this.pendingInit.reject(err)
      for (const pending of this.pending.values()) {
        pending.reject(err)
      }
      this.pending.clear()
    }
  }

  private routeInboundMessage(message: JsonRpcInbound): void {
    if ('id' in message && ('result' in message || 'error' in message)) {
      const request = this.pending.get(message.id)
      if (!request) {
        return
      }
      this.pending.delete(message.id)
      if ('error' in message) {
        const failure = message as JsonRpcFailure
        request.reject(new Error(failure.error.message))
      } else {
        const success = message as JsonRpcSuccess
        request.resolve(success.result)
      }
      return
    }
    if ('method' in message && !('id' in message)) {
      this.notificationHandler(message as JsonRpcNotification)
    }
  }

  // Used by tests to verify init behavior.
  isReady(): boolean {
    return this.initialized
  }
}
