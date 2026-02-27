# Language Server Protocol (LSP)

The snaq-lite LSP server powers IDE features (diagnostics, hover, inlay hints) for the snaq-lite language. The same server runs as a **native** process (stdio) or inside a **Web Worker** (WASM) in the browser.

## Capabilities

- **Initialize / Initialized** — Handshake and capability negotiation.
- **Text document sync** — Full document sync on open and change.
- **Diagnostics** — Parse and resolve errors are reported as LSP diagnostics (e.g. red squiggles). Errors include source location (line/column). Positions use 0-based line and **byte offset** as character (consistent with the language’s span representation).
- **Hover** — At a position, shows the evaluated value (numeric, symbolic, or formatted) for the expression under the cursor.
- **Inlay hints** — Inline hints after expressions showing the computed value (e.g. `→ 5` or `→ 3 m`).
- **Live result pub-sub** — Custom methods `snaqlite/subscribe`, `snaqlite/unsubscribe`, and server-to-client notification `snaqlite/publishResult` for streaming or one-shot results. See [Pub-sub (live results)](#pub-sub-live-results) below.

## Pub-sub (live results)

The server supports subscribing to the **root result** of the current document. When the result is a vector (e.g. from a literal or from `$name`), the server streams batches to the client; otherwise it sends a single `Completed` notification.

### Methods

| Method | Type | Payload | Response / effect |
|--------|------|--------|------------------|
| `snaqlite/subscribe` | Request | `{ textDocument: { uri }, range?: Range }` (range optional; root-only in Phase 1) | `{ subscriptionId: string }` or error |
| `snaqlite/unsubscribe` | Request | `{ subscriptionId: string }` | `null` or error |
| `snaqlite/publishResult` | Notification (server → client) | `{ subscriptionId, status, data? }` | — |

**Status:** `"Running"` \| `"Completed"` \| `"Error"` \| `"Cancelled"`.

**Data (wire format):**

- **Running:** `{ elements: Array<element>, offset?: number, count?: number }`. Each `element` is either `{ display: string }`, `null` (undefined), or `{ kind: "error", message: string }`.
- **Completed:** optional `{ display?: string, totalElements?: number }`.
- **Error:** `{ message: string }`.
- **Cancelled:** optional `{ reason?: string }` (e.g. `"Document changed"`).

### Lifecycle

- **Subscribe:** Client sends `snaqlite/subscribe` with the document URI. The server runs the document (root-only); if the result is a vector, it spawns a background consumer and returns a `subscriptionId`. The client then receives `snaqlite/publishResult` with status `Running` (batches) and finally `Completed` or `Error`.
- **Unsubscribe:** Client sends `snaqlite/unsubscribe` with `subscriptionId`. The server cancels the consumer and stops sending for that subscription.
- **Document change:** On `textDocument/didChange` (or open), the server invalidates all subscriptions for that URI and sends `snaqlite/publishResult` with status `Cancelled` and reason `"Document changed"` for each.

Clients should send `snaqlite/unsubscribe` when closing the file or hiding the results panel.

## Native (stdio)

Build and run the LSP binary. The IDE starts it as a subprocess and talks over stdin/stdout.

```bash
cargo build -p snaq-lite-lsp --release
# Then point your IDE's "snaq-lite" language server to the binary, e.g.:
# ./target/release/snaq-lite-lsp
```

The server uses the Language Server Protocol over standard input/output. No extra configuration is required beyond telling the client the command path.

## WASM (Web Worker)

The server can run inside a Web Worker so the IDE (e.g. in the browser) does not block the main thread.

1. **Build the WASM module** (library only):

   ```bash
   cargo build -p snaq-lite-lsp --target wasm32-unknown-unknown --lib
   wasm-pack build crates/snaq-lite-lsp --target web --out-dir dist-lsp
   ```

   (Or use your preferred way to produce a WASM module that exports the LSP entry.)

2. **Load the module in a Worker** and call the exported start function:

   - **`startSnaqLiteLsp(postMessageCallback)`** — Starts the LSP server. Pass a JS function that will be called with each response string; the host should send that string to the IDE (e.g. `self.postMessage(result)`).
   - **`pushLspMessage(str)`** — Call this from the Worker’s `onmessage` with the raw LSP request string (e.g. the JSON-RPC message from the IDE). Each time the IDE sends a message, the host pushes it with `pushLspMessage(event.data)`.

3. **Message format** — Messages are JSON-RPC (LSP over JSON-RPC). The host is responsible for forwarding:
   - IDE → Worker: pass the received string to `pushLspMessage(s)`.
   - Worker → IDE: for each string passed to `postMessageCallback`, call `self.postMessage(s)` (or equivalent) so the IDE receives the response.

## Verification

- **Native:** Unit tests (span→range, run_error→diagnostic) and integration tests run the server in-process with mock stdio: `native_initialize_returns_capabilities` (initialize and capabilities), `native_did_open_and_hover_returns_value` (hover). **Pub-sub** is covered by: `native_subscribe_scalar_returns_id_and_completed`, `native_subscribe_vector_returns_id_and_stream_completes`, `native_subscribe_then_unsubscribe_succeeds`, `native_subscribe_then_did_change_receives_cancelled`, and `native_subscribe_wrong_uri_returns_error` (subscribe with non-open URI returns invalid_params).
- **WASM:** Build the lib for `wasm32-unknown-unknown` and use `startSnaqLiteLsp` / `pushLspMessage` in a Web Worker; capability negotiation and diagnostics can be verified manually or via a browser/Node test harness.

## Limits and edge cases

- **Single document** — The server tracks one document (URI). Opening or changing another document replaces the tracked one.
- **Pub-sub** — Subscriptions are root-only (whole-document result). Subscribing to a range is not yet supported. Stream input source for `$name` is not in subscribe params (Phase 1); the server runs with empty stream inputs, so unbound `$name` yields a run error. On WASM, vector results are sent as a single `Completed` notification (no streaming). Document change cancels all subscriptions for that URI. On server shutdown, all subscriptions are cancelled and each client receives `Cancelled` with reason `"Server shutdown"`.
- **Full sync** — Only full-document sync is used; incremental sync is not implemented. A `didChange` with an empty `content_changes` array is a no-op.
- **Diagnostics** — Parse and resolve/simplify errors are reported; optional runtime validation can add more. No debouncing; every change triggers a new diagnostic run.
- **Hover / inlay** — Depend on the current Salsa program and source; if the document has parse errors, hover and inlay may be empty or partial.
