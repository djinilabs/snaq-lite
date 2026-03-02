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
let resolveClient: ((c: LanguageClientLike) => void) | null = null
const clientPromise = new Promise<LanguageClientLike>((resolve) => {
  resolveClient = resolve
})

/** Callbacks to run once when the client is set (e.g. pending graph sync after load). */
const whenReadyCallbacks: Array<() => void> = []

export function setLanguageClient(c: LanguageClientLike | null): void {
  client = c
  if (typeof window !== 'undefined') {
    ;(window as unknown as { __E2E_LSP_READY__?: boolean }).__E2E_LSP_READY__ = c != null
  }
  if (c != null && resolveClient != null) {
    resolveClient(c)
    resolveClient = null
  }
  if (c != null && whenReadyCallbacks.length > 0) {
    const fns = [...whenReadyCallbacks]
    whenReadyCallbacks.length = 0
    for (const fn of fns) fn()
  }
}

/**
 * Runs the callback when the client is available: immediately if already set,
 * otherwise once when setLanguageClient is next called with a non-null client.
 */
export function whenClientReady(cb: () => void): void {
  if (client != null) {
    cb()
    return
  }
  whenReadyCallbacks.push(cb)
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

/**
 * Returns a promise that resolves with the client when it is set, or null after timeoutMs.
 * Use when the user action (e.g. connecting an edge) may happen before the LSP has finished initializing.
 */
export function waitForLanguageClient(timeoutMs: number): Promise<LanguageClientLike | null> {
  if (client != null) return Promise.resolve(client)
  return Promise.race([
    clientPromise,
    new Promise<null>((resolve) => setTimeout(() => resolve(null), timeoutMs)),
  ])
}
