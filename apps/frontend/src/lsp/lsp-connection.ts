/**
 * LSP connection over the Web Worker: push-based reader and writer that use the message router.
 * Used to create a single MessageConnection so the app can sendRequest/sendNotification
 * and receive responses and notifications (e.g. publishDiagnostics).
 */

import type { DataCallback } from 'vscode-jsonrpc'
import type { Message } from 'vscode-jsonrpc'
import type { Disposable } from 'vscode-jsonrpc'
import {
  AbstractMessageReader,
  AbstractMessageWriter,
  createMessageConnection,
  type MessageConnection,
} from 'vscode-jsonrpc'

/**
 * Message reader that stores the listen callback and exposes push(raw) to feed incoming messages.
 * Used when the transport is postMessage: we push each worker message string here after routeMessage.
 */
class PushMessageReader extends AbstractMessageReader {
  private callback: DataCallback | null = null

  listen(callback: DataCallback): Disposable {
    this.callback = callback
    return {
      dispose: () => {
        this.callback = null
      },
    }
  }

  /** Call with raw JSON-RPC string from the worker. Parses and forwards to the listen callback. */
  push(raw: string): void {
    if (!this.callback) return
    try {
      const msg = JSON.parse(raw) as Message
      this.callback(msg)
    } catch {
      // invalid JSON; skip
    }
  }
}

/**
 * Message writer that sends each message as a JSON string via the given send function (e.g. sendToWorker).
 */
class WorkerMessageWriter extends AbstractMessageWriter {
  constructor(private readonly send: (msg: string) => void) {
    super()
  }

  async write(msg: Message): Promise<void> {
    try {
      this.send(JSON.stringify(msg))
    } catch (error) {
      this.fireError(error as Error, msg, 1)
      throw error
    }
  }

  end(): void {
    // no-op; worker channel stays open
  }
}

export interface LspConnectionResult {
  connection: MessageConnection
  push: (raw: string) => void
}

/**
 * Creates a MessageConnection (reader + writer) that uses the given send function for outgoing
 * messages. Incoming messages must be pushed via the returned push(raw) after the connection is listening.
 */
export function createLspConnection(send: (msg: string) => void): LspConnectionResult {
  const reader = new PushMessageReader()
  const writer = new WorkerMessageWriter(send)
  const connection = createMessageConnection(reader, writer)
  return {
    connection,
    push: (raw: string) => reader.push(raw),
  }
}
