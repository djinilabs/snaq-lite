/**
 * Module singleton for the LSP language client. Set after the connection is started
 * (initialize handshake done). Used by edge-handlers and presentation-block so they
 * can sendRequest/sendNotification without React context.
 */

export interface LanguageClientLike {
  sendRequest: <T = unknown>(method: string, params?: unknown) => Promise<T>
  sendNotification: (method: string, params?: unknown) => void
}

let client: LanguageClientLike | null = null

export function setLanguageClient(c: LanguageClientLike | null): void {
  client = c
}

export function getLanguageClient(): LanguageClientLike {
  if (!client) {
    throw new Error('Language client not initialized; ensure LspProvider has mounted and worker is ready.')
  }
  return client
}

export function hasLanguageClient(): boolean {
  return client != null
}
