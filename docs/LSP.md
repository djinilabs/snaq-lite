# Language Server Protocol (LSP)

The snaq-lite LSP server powers IDE features (diagnostics, hover, inlay hints) for the snaq-lite language. The same server runs as a **native** process (stdio) or inside a **Web Worker** (WASM) in the browser.

## Capabilities

- **Initialize / Initialized** — Handshake and capability negotiation.
- **Text document sync** — Full document sync on open and change.
  (The server advertises incremental sync and applies `didChange` ranges when provided.)
- **Diagnostics** — Parse and resolve errors are reported as LSP diagnostics (e.g. red squiggles). Errors include source location (line/column). Positions use 0-based line and **byte offset** as character (consistent with the language’s span representation).
- **Hover** — At a position, shows the evaluated value (numeric, symbolic, or formatted) for the expression under the cursor.
- **Inlay hints** — Inline hints after expressions showing the computed value (e.g. `→ 5` or `→ 3 m`).
- **Live result pub-sub** — Custom methods `snaqlite/subscribe`, `snaqlite/unsubscribe`, and server-to-client notification `snaqlite/publishResult` for streaming or one-shot results. See [Pub-sub (live results)](#pub-sub-live-results) below.

## Pub-sub (live results)

The server supports subscribing to the **root result** of the current document. When the result is a vector (e.g. from a literal or from `$name`), the server streams batches to the client; otherwise it sends a single `Completed` notification.

### Methods

| Method | Type | Payload | Response / effect |
| --- | --- | --- | --- |
| `snaqlite/subscribe` | Request | `{ textDocument: { uri }, range?: Range }` (range optional; root-only in Phase 1) | `{ subscriptionId: string }` or error |
| `snaqlite/unsubscribe` | Request | `{ subscriptionId: string }` | `null` or error |
| `snaqlite/publishResult` | Notification (server → client) | `{ subscriptionId, status, data? }` | — |
| `snaqlite/subscribeNode` | Request | `{ sourceUri }` | `{ subscriptionId: string }` or error |
| `snaqlite/unsubscribeNode` | Request | `{ subscriptionId: string }` | `null` or error |
| `snaqlite/publishNodeResult` | Notification (server → client) | Same payload as `snaqlite/publishResult` | — |

**Status:** `"Running"` \| `"Completed"` \| `"Error"` \| `"Cancelled"`.

**Data (wire format):**

- **Running:** `{ elements: Array<element>, offset?: number, count?: number }`. Each `element` is either `{ display: string }`, `null` (undefined), or `{ kind: "error", message: string }`.
- **Completed:** optional `{ display?: string, totalElements?: number }`.
- **Error:** `{ message: string }`.
- **Cancelled:** optional `{ reason?: string }` (e.g. `"Document changed"`).

`subscribeNode`/`unsubscribeNode` are the canonical node-centric APIs. `subscribe`/`unsubscribe` remain supported for compatibility and use the same runtime pipeline.

### Lifecycle

- **Subscribe:** Client sends `snaqlite/subscribeNode` (or legacy `snaqlite/subscribe`) for a node URI.
  - `subscribeNode` evaluates with graph inputs (upstream wiring applied).
  - Legacy `subscribe` evaluates document root with empty stream inputs (no graph wiring).
  - If the result is a vector, the server spawns a background consumer and returns a `subscriptionId`. The client receives both `snaqlite/publishResult` and `snaqlite/publishNodeResult` with status `Running` (batches on native) and finally `Completed` or `Error`.
- **Unsubscribe:** Client sends `snaqlite/unsubscribeNode` (or legacy `snaqlite/unsubscribe`) with `subscriptionId`. The server cancels the consumer and stops sending for that subscription.
- **Document change:** On `textDocument/didChange` (or open), the server recomputes impacted nodes and pushes fresh `Completed` / `Error` updates for active subscriptions/widgets on affected URIs.

Clients should send `snaqlite/unsubscribe` when closing the file or hiding the results panel.

## Visual computation graph

The server supports a **visual computation graph** (DAG): each **Computation Box** is a node identified by a **virtual document URI** (e.g. `snaq://graph/node_42.sl`). The frontend uses a **single shared LSP connection** (vscode-jsonrpc MessageConnection over the Web Worker message router). It opens virtual URIs with `textDocument/didOpen` and sends `didChange`; the server keeps multi-document state keyed by URI. Diagnostics, hover, and inlay hints are provided by the LSP over the same connection; the frontend applies `textDocument/publishDiagnostics` to Monaco via `setModelMarkers`. Nodes can declare **input ports** and be **wired** together; **Presentation Blocks** (widgets) subscribe to a node’s output and receive live stream or one-shot updates.

### Virtual URIs and multi-document state

- Documents are keyed by URI. Any URI is valid (e.g. `file:///...` or `snaq://graph/<id>.sl`). There is no special parsing for virtual schemes; only the state map is per-URI.
- On `didOpen` / `didChange` the server updates the entry for that URI (source, version, diagnostics, root definition). Diagnostics and hover use the same URI to look up the document.

### Node signature (input/output ports)

- **Input declarations** — At the start of a block, nodes can declare typed inputs, e.g. `input revenue: ProbabilisticTensor` and `input count: Vector`. These are syntactic only (no runtime type checking in the language); the same names are used as `$name` for stream inputs.
- **Notification `snaqlite/graph/nodeSignatureUpdated`** — After each `didOpen` / `didChange` for a URI, the server sends this notification with:
  - `uri` (string)
  - `inputs`: array of `{ name, paramId, type }` (declared input ports; `paramId` is stable across rename)
  - `outputType`: optional string (e.g. `"Vector"`, `"Numeric"`) inferred from graph-aware execution (upstream inputs applied when wired), or `null` if not available.

The frontend can use this to draw input/output anchors on the canvas.

### Graph wiring and type safety

- **Request `snaqlite/graph/connect`** — Params: `sourceUri`, `targetUri`, `targetInputName`. `targetInputName` can be either display name or stable `paramId`. The server resolves both URIs to open documents, rejects cycle-creating connects, infers source output with graph-aware execution, and verifies type compatibility (exact type name match; target `Undefined` accepts any). On success it adds or replaces the edge (at most one source per target input/paramId). On type mismatch it returns JSON-RPC error `-32001` (`"Type mismatch"`). On cycle it returns server error `-32002`.
- **Request `snaqlite/graph/disconnect`** — Params: `targetUri`, `targetInputName`. Removes the edge for that target and input. Widgets subscribed to the target node are invalidated (see reactive invalidation).

Running a node with graph inputs: when the server needs a node’s result (for `nodeSignatureUpdated` output type or for `subscribeWidget`), it topologically sorts the subgraph that includes that node, runs each ancestor node in order, creates stream handles for vector outputs so downstream nodes can read them, then runs the target node with `stream_inputs` built from the graph edges.

### Widget subscriptions (Presentation Blocks)

- **Request `snaqlite/graph/subscribeWidget`** — Params: `widgetId`, `sourceUri`. The server runs the source node with graph inputs (topological run of the subgraph, stream inputs from upstream node outputs). The result is **cached** per widget. The server sends a single **Completed** notification with a summary (no streaming of vector elements). The client can then request slices via `snaqlite/graph/fetchResultSlice` for virtualized list/table views.
- **Notification `snaqlite/graph/widgetDataUpdate`** — Params: `widgetId`, `status` (`"Running"` | `"Completed"` | `"Cancelled"` | `"Error"`), optional `payload`. For **Completed**, the payload includes:
  - **`display`** (optional) — Formatted value for scalars or when a single value is shown.
  - **`totalElements`** (optional) — Number of elements (vectors) or keys (maps).
  - **`resultType`** (optional) — `"Scalar"` | `"Vector"` | `"Map"` | `"Undefined"` so the client can show a type-aware summary and open a detail modal.
  - **`resultSummary`** (optional) — For vectors: `{ length: number }`. For maps: `{ keys?: string[], keyCount?: number }` (keys only if small).
- **Request `snaqlite/graph/unsubscribeWidget`** — Params: `widgetId`. Removes the widget and clears its cached result; sends a final `widgetDataUpdate` with status `Cancelled`.
- **Request `snaqlite/graph/fetchResultSlice`** — Fetches a paginated slice of the cached result at an optional **path** (for nested vectors/maps).  
  - **Params:** `widgetId` (string), `path` (array of path segments: **0-based** numbers for vector indices, strings for map keys; empty array = root), `offset` (number), `limit` (number).  
  - **Response:** `elements` (array of slice elements), `totalCount` (number), `hasMore` (boolean).  
  - **Slice elements:** Scalars are `{ display: string }`. Nested vectors are `{ type: "vector", path: PathSegment[] }` so the client can request that path with offset/limit. Nested maps are `{ type: "map", path: PathSegment[], keys?: string[], keyCount?: number }`. Map rows are `{ key: string, value: ResultSliceElement }`.  
  - Path semantics: **0-based** indices for vectors (e.g. `[5]` = 6th element). Map entries are sliced in **registration order**. For replayable lazy vectors, slices are computed with a streaming window (count + window in one pass) instead of full vector materialization. If the widget is not found or the path is invalid, the server returns an error.

Multiple widgets on the same node each get their own run and cached result.

Notifications can include metadata fields:

- `revision` (monotonic per-node recompute revision),
- `canvasId` (active canvas identity),
- `uri` (document/node URI the update belongs to).

### Reactive updates and lifecycle

- **Document change** — On `didChange` / `didOpen` for a URI, the server reconciles graph inputs, recomputes impacted nodes, and pushes fresh `Completed` / `Error` updates to active subscriptions/widgets for affected nodes.
- **Document close** — On `didClose` for a URI, the server removes the document from state, removes graph edges where the URI is source/target, clears cached node result, cancels subscriptions/widgets bound to that URI (`Cancelled` with reason `"Document closed"`), and recomputes downstream dependents.
- **Edge removal** — When `snaqlite/graph/disconnect` is called, the server removes the edge and invalidates all widget subscriptions for the target URI (cancel and send `widgetDataUpdate` Cancelled). The UI triggers disconnect when the user deletes an edge (e.g. select edge and Backspace).
- Connect failure (type mismatch) does not add an edge, so no invalidation is needed.

### Namespace reset (soft canvas isolation)

For URI-namespace based canvas isolation, the server exposes:

- **Request `snaqlite/graph/resetNamespace`** — Params: `{ uriPrefix: string }`.
  - Removes all open documents with URI starting with `uriPrefix`.
  - Removes graph edges whose source or target URI starts with `uriPrefix`.
  - Removes node-result cache entries for matching URIs.
  - Cancels matching subscriptions/widgets (`Cancelled`, reason `"Namespace reset"`).
  - Recomputes remaining downstream nodes that depended on removed sources.
  - Response: `{ removedDocuments: number }`.

### Canvas isolation (hard binding)

- The first used URI binds the LSP instance to a single canvas identity.
- Later graph/subscription/document operations with a different canvas identity are rejected.
- For `snaq://` URIs, canvas identity is the URI host (example: `snaq://canvas-a/node_1.sl` -> `canvas-a`).

### Canonical canvas snapshot

- **Request `snaqlite/graph/exportCanvasDocument`** — Params: `{}`.
  - Response: `{ canvasDocument }`, where `canvasDocument` contains:
    - `canvasId` (optional),
    - `nodes[]`: `{ uri, source, version? }`,
    - `edges[]`: `{ sourceUri, targetUri, targetParamId }`.
- **Request `snaqlite/graph/importCanvasDocument`** — Params: `{ canvasDocument }`.
  - Replaces in-memory runtime state with the supplied snapshot.
  - Cancels active subscriptions/widgets (`reason: "Canvas import"`), clears node-result cache, imports documents/edges, recomputes imported nodes, and republishes diagnostics/signatures.
  - Response: `{ importedNodes, importedEdges }`.

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

1. **Build the WASM module** (library only). From the repo root:

   ```bash
   pnpm run build:lsp-wasm
   ```

   The release build runs `wasm-opt` (from [Binaryen](https://github.com/WebAssembly/binaryen)) to optimize the WASM. Install it if needed: **macOS** `brew install binaryen`, **Ubuntu/Debian** `apt install binaryen`.

   Or manually (from repo root; wasm-pack resolves `--out-dir` relative to the crate):

   ```bash
   cargo build -p snaq-lite-lsp --target wasm32-unknown-unknown --lib
   wasm-pack build crates/snaq-lite-lsp --target web --out-dir ../../apps/frontend/public/lsp-wasm
   ```

   Output is under `apps/frontend/public/lsp-wasm/` (e.g. `snaq_lite_lsp.js`, `snaq_lite_lsp_bg.wasm`). The frontend loads the script at `{origin}{BASE_URL}lsp-wasm/snaq_lite_lsp.js`.

2. **Worker init protocol.** The main thread must send a **control message** first (not LSP):

   - **Main → Worker:** `{ type: 'init', wasmUrl: string }` — the URL of the wasm-pack JS entry (e.g. the `snaq_lite_lsp.js` script). The worker then dynamically imports that URL, calls the default init, then `start_snaq_lite_lsp(postMessageCallback)`.
   - **Worker → Main (success):** `{ type: 'snaqlite-worker-ready' }` — the LSP is running; the main thread can set “worker ready” and forward LSP traffic.
   - **Worker → Main (failure):** `{ type: 'snaqlite-worker-error', error: string }` — load or init failed; the main thread should set worker not ready and surface the error.

   All other messages are raw LSP JSON-RPC strings (main → worker: request/notification; worker → main: response/notification).

3. **WASM exports** (from the wasm-pack module):

   - **`default`** — Async init function (loads the `.wasm`). Call once before `start_snaq_lite_lsp`.
   - **`start_snaq_lite_lsp(postMessageCallback)`** — Starts the LSP server. Pass a JS function that will be called with each response string; the host should send that string to the main thread (e.g. `self.postMessage(result)`).
   - **`push_lsp_message(str)`** — Call this from the Worker’s `onmessage` with the raw LSP request string. Each time the main thread sends a message, the worker pushes it with `push_lsp_message(event.data)`.

4. **Message format** — After ready, messages are JSON-RPC (LSP over JSON-RPC):
   - Main → Worker: pass the received string to `worker.postMessage(string)`; the worker forwards it to `push_lsp_message(s)`.
   - Worker → Main: for each string passed to `postMessageCallback`, the worker does `self.postMessage(s)` so the main thread receives the response and routes it (e.g. to the LSP client or to the graph/widget stores).

## Verification

- **Native:** Unit tests (span→range, run_error→diagnostic, graph state connect/disconnect/topological_order, widget registry) and integration tests run the server in-process with mock stdio: `native_initialize_returns_capabilities` (initialize and capabilities), `native_did_open_and_hover_returns_value` (hover). **Pub-sub** is covered by: `native_subscribe_scalar_returns_id_and_completed`, `native_subscribe_vector_returns_id_and_stream_completes`, `native_subscribe_then_unsubscribe_succeeds`, `native_subscribe_then_did_change_receives_cancelled`, and `native_subscribe_wrong_uri_returns_error` (subscribe with non-open URI returns invalid_params). **Visual computation graph:** multi-document (open two virtual URIs, hover in each), connect (success and type mismatch error), subscribeWidget / widgetDataUpdate (Running, Completed, Cancelled), unsubscribeWidget, and didChange → Cancelled for affected widgets.
- **WASM:** Build the lib for `wasm32-unknown-unknown` and use `startSnaqLiteLsp` / `pushLspMessage` in a Web Worker; capability negotiation and diagnostics can be verified manually or via a browser/Node test harness.

## Limits and edge cases

- **Multi-document** — The server tracks a map of URI → document. Opening or changing a document creates or updates the entry for that URI; virtual URIs (e.g. `snaq://graph/...`) are supported the same way as file URIs.
- **Pub-sub** — Subscriptions are root-only (whole-document result). Subscribing to a range is not yet supported. Stream input source for `$name` is not in subscribe params (Phase 1); the server runs with empty stream inputs, so unbound `$name` yields a run error. On WASM, vector subscriptions do not stream element batches, but status notifications follow `Running` then `Completed` for lifecycle parity. For canvas/UI result browsing and pagination, use `snaqlite/graph/subscribeWidget` + `snaqlite/graph/fetchResultSlice`.
- **Vector summary on WASM** — For some lazy vector kinds, `resultSummary.length` / `totalElements` in Completed payload may be omitted until data is materialized. Clients should rely on `fetchResultSlice` for authoritative pagination metadata.
- **Incremental sync** — The server uses incremental text sync (`TextDocumentSyncKind::INCREMENTAL`) and supports full-text replacement fallback when range is omitted. A `didChange` with an empty `content_changes` array is a no-op.
- **Input declaration runtime semantics** — Native and WASM intentionally differ for declared `input` bindings: native preserves scalar-friendly binding for single-item inputs, while WASM keeps lazy vector/stream binding to avoid blocking the worker event loop.
- **Diagnostics** — Parse and resolve/simplify errors are reported; optional runtime validation can add more. No debouncing; every change triggers a new diagnostic run.
- **Hover / inlay** — Depend on the current Salsa program and source; if the document has parse errors, hover and inlay may be empty or partial.
