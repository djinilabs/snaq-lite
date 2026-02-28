/**
 * LSP Web Worker entry. Loads WASM LSP and forwards messages.
 * Stub: when WASM is not yet loaded, responds to initialize so the client can handshake.
 * Production: import WASM, call startSnaqLiteLsp((str) => self.postMessage(str)),
 * and in onmessage call pushLspMessage(event.data).
 */

const postMessageCallback = (response: string) => {
  self.postMessage(response)
}

// Stub: no WASM loaded yet. Reply to initialize so client does not hang.
self.onmessage = (event: MessageEvent<string>) => {
  try {
    const msg = JSON.parse(event.data) as { jsonrpc?: string; id?: string | number; method?: string }
    if (msg.jsonrpc === '2.0' && msg.method === 'initialize') {
      const response = {
        jsonrpc: '2.0' as const,
        id: msg.id,
        result: {
          capabilities: {
            textDocumentSync: 1,
            hoverProvider: true,
          },
        },
      }
      postMessageCallback(JSON.stringify(response))
      return
    }
    if (msg.jsonrpc === '2.0' && msg.method === 'initialized') {
      // No response needed for notification
      return
    }
  } catch {
    // ignore
  }
  // When WASM is integrated: pushLspMessage(event.data) here
}
