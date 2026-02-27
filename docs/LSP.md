# Language Server Protocol (LSP)

The snaq-lite LSP server powers IDE features (diagnostics, hover, inlay hints) for the snaq-lite language. The same server runs as a **native** process (stdio) or inside a **Web Worker** (WASM) in the browser.

## Capabilities

- **Initialize / Initialized** — Handshake and capability negotiation.
- **Text document sync** — Full document sync on open and change.
- **Diagnostics** — Parse and resolve errors are reported as LSP diagnostics (e.g. red squiggles). Errors include source location (line/column). Positions use 0-based line and **byte offset** as character (consistent with the language’s span representation).
- **Hover** — At a position, shows the evaluated value (numeric, symbolic, or formatted) for the expression under the cursor.
- **Inlay hints** — Inline hints after expressions showing the computed value (e.g. `→ 5` or `→ 3 m`).

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

- **Native:** Unit tests (span→range, run_error→diagnostic) and an integration test (`native_initialize_returns_capabilities`) run the server in-process with mock stdio, send an `initialize` request, and assert the response includes capabilities (e.g. `hoverProvider`, `textDocumentSync`).
- **WASM:** Build the lib for `wasm32-unknown-unknown` and use `startSnaqLiteLsp` / `pushLspMessage` in a Web Worker; capability negotiation and diagnostics can be verified manually or via a browser/Node test harness.

## Limits and edge cases

- **Single document** — The server tracks one document (URI). Opening or changing another document replaces the tracked one.
- **Full sync** — Only full-document sync is used; incremental sync is not implemented. A `didChange` with an empty `content_changes` array is a no-op.
- **Diagnostics** — Parse and resolve/simplify errors are reported; optional runtime validation can add more. No debouncing; every change triggers a new diagnostic run.
- **Hover / inlay** — Depend on the current Salsa program and source; if the document has parse errors, hover and inlay may be empty or partial.
