# External data as streams

Programs can refer to **external stream inputs** using the `$name` syntax. The Host supplies data by pushing **chunks** into a channel and registering the stream handle under that name. Evaluation returns a **pipeline** (a vector description); the Host then consumes the resulting stream while pushing data.

## Syntax: `$name`

- **Syntax:** `$` followed by an identifier (e.g. `$sales_data`, `$readings`).
- **Meaning:** The expression denotes an external stream identified by `name`. The name is looked up in a **stream input registry** provided by the Host at run time. The registry maps names to **stream handles**, not to the data itself.
- **Use in expressions:** You can use `$name` anywhere a vector is valid. For example: `$sales_data * 2`, `$readings.sum()`, `take($log, 0, 100)`.
- **Browser (WASM):** When a computation input is wired from a file block, you **must** use `$name` in the expression (e.g. `$aa * 10`). Do not use the bare name `aa` — the stream is not bound to the identifier in the browser, so `aa * 10` would fail or hang.

If the Host runs a program that uses `$name` but does **not** set the stream input registry (or does not register that name), evaluation fails with **unbound stream input: name**.

## Chunk format

The Host pushes data in **chunks**. Each chunk is a list of elements in the runtime’s value format:

- Each element is one of: `Ok(Some(value))` for a normal value, `Ok(None)` for a missing/undefined element, or `Err(run_error)` for an error.
- A chunk is a vector of such elements (e.g. up to 10,000 rows at a time). The Host is responsible for chunk size and I/O (e.g. reading Parquet or CSV in batches and converting to this format).

**End of stream:** The Host signals end-of-stream by closing/dropping the sender (or equivalent). The runtime then treats the stream as complete.

## Host workflow

1. **Create a channel** (bounded sender/receiver; see **Back-pressure** in WASM Host) whose items are **chunks** in the format above.
2. **Register the receiver:** Call the library’s **register** function with the receiver; it returns a **stream handle id**. The receiver is single-consumer: it is taken by the runtime when the stream is driven.
3. **Build the stream input map:** Map each name used in the program (e.g. `"sales_data"`) to the corresponding stream handle id.
4. **Run with stream inputs:** Call **run_with_stream_inputs**(input, unit_registry, stream_input_map). You get back the evaluated **Value** and the **database**. If the result is a vector (e.g. `$sales_data * 2`), it is a pipeline that reads from the registered stream.
5. **Consume the stream:** If the result is a vector, call **vector_into_stream** with the database and the vector’s inner pipeline. This returns a stream that yields elements (or errors). Drive this stream (e.g. in an async loop) while, in parallel, pushing chunks on the sender from your I/O (files, network, etc.). When you have no more data, close the sender to signal EOF.
6. **Edge cases:** Programs that use only external streams (e.g. root is `$x * 2`) do not produce a single numeric quantity; operations like **run_numeric** are not applicable for such programs. Use **run_with_stream_inputs** and then consume the vector stream as above.

## Limits and platform

- **run_numeric / to_quantity:** When the program result is a vector from an external stream (e.g. `$x * 2`), the result is a pipeline, not a single quantity. Requesting a numeric result for such a program is not supported; use **run_with_stream_inputs** and consume the vector stream instead.
- **Stream handle is single-consumer:** Each registered receiver is taken by the runtime when you call **vector_into_stream** on a pipeline that uses that input. Calling **vector_into_stream** again on the same pipeline (or another expression that uses the same `$name`) will not see the data again; the stream yields one error (**stream input not available (already consumed or not registered)**) then completes.
- **Graph fan-out:** In the LSP/graph UI, when one computation output is wired to **multiple inputs** of another computation, the runtime creates **one stream handle per edge** and feeds a copy of the upstream value (scalar or vector) to each handle. So fan-out (one output → many inputs) works without consuming the same handle twice.
- **WASM:** The stream handle registry is thread-local. On WASM, drive the stream in an async task (e.g. with `wasm-bindgen-futures` or your async runtime) so that the main thread is not blocked. Chunked push and consumption work the same as on native targets.

## WASM Host (browser)

When the runtime runs as WebAssembly in the browser, the Host has no access to the native file system. Data must come from browser APIs (e.g. `fetch()` response body, `File.stream()` from an file input). The WASM build exposes a Host API that uses **single-threaded async**: channels and streams are driven via `wasm-bindgen-futures` so the main thread is not blocked and the UI stays responsive.

### Back-pressure

The stream channel is **bounded** (capacity 4 chunks). When the channel is full, **send** in the feeder yields until the consumer drains a chunk. So the feeder is back-pressured and never pushes as fast as possible, which keeps memory bounded for large files.

### I/O safeguards

- **No file paths:** All input is from JS: pass a URL or a `ReadableStream` (e.g. `response.body` or `file.stream()`) to the worker via **feedStreamFromUrl** or **feedStreamFromReadableStream**, or build chunks in JS and call `pushChunk(streamIndex, array)`.
- **Memory limit:** WASM is constrained to a 4GB address space. The Host must not load entire files into memory; use chunked reading and fixed-size batches (e.g. 8,192 rows per chunk when parsing). Bounded send ensures the feeder does not run ahead of the consumer.
- **Event-loop yielding:** The consumer and feeder yield to the browser event loop periodically (consumer: every 16 elements; feeder: every 4 read calls) so the tab can paint and handle input. These intervals are fixed; a future version could expose them as options.
- **Indices:** Stream and run indices are not reclaimed; slots grow with use over the page lifetime. For long-lived apps with many runs, consider reusing a small set of stream inputs where possible.

### Host API (WASM)

- **createStreamInput()** → `streamIndex` (number). Creates a channel and registers the receiver; the Host uses the returned index in the stream input map and for pushing data.
- **runWithStreamInputs(script, streamInputMap)** → `{ runIndex, isVector }`. `streamInputMap` is a JS object mapping stream names to **non-negative integer** stream indices from `createStreamInput` (e.g. `{ data: 0 }`). Returns a run index for consumption.
- **pushChunk(streamIndex, array)** — Push a chunk: `array` is a JS array of numbers (or `null` for sparse). Converts to scalar dimensionless values (variance 0). Fails if the stream was already closed.
- **closeStream(streamIndex)** — Signal end-of-stream for that stream. After this, `pushChunk` for this index will fail.
- **startFeeder(streamIndex, readableStream)** — Start an async task that reads from the JS `ReadableStream`, parses **newline-delimited numbers**, pushes chunks with **send().await** (back-pressure), and drops the sender when done.
- **startCsvFeeder(streamIndex, readableStream)** — Same as above but parses **CSV**: first line = headers, rest = data rows; each row is converted to a **map** (column name → number). Pushes row-as-map chunks with back-pressure. Delimiter is comma or semicolon (auto-detected from first line).
- **pushChunkMaps(streamIndex, rowsJs)** — Push a chunk of row-as-map values from JS (array of objects: each object = column name → number). Used when the client has already parsed rows and wants to push map chunks.
- **Format hint:** The worker messages **feedStreamFromUrl** and **feedStreamFromReadableStream** accept an optional **format** (`"numeric"` | `"csv"`). When `format === "csv"`, the worker calls **startCsvFeeder** instead of **startFeeder**. The client infers format from URL (e.g. `.csv`) or file type (e.g. `text/csv`).
- **consumeOutputStream(runIndex, onChunk, onDone, onError)** — Drive the output stream: `onChunk(element)` for each element (number for numeric, `null` for sparse/undefined, or object `{ uncertain: p }` for fuzzy boolean), `onDone()` at end, `onError(message)` when the run result is invalid or the stream yields an error. Yields every 16 elements. **Callbacks must not throw**; if they do, behavior is unspecified.

### Host execution loop

1. **Initialization:** For each `$name` used in the script, call `createStreamInput()` and build a map from name to stream index (e.g. `{ data: createStreamInput() }`).
2. **Pipeline construction:** Call `runWithStreamInputs(script, streamInputMap)`. This runs Salsa synchronously and returns the terminal value (and a run index). If the result is a vector, it is a pipeline that will read from the registered streams.
3. **Feeder task:** For each stream that is backed by a byte source, call `startFeeder(streamIndex, readStream)` so the Host reads from the stream, parses in chunks, yields to the event loop, and pushes chunks. Alternatively, parse in JS and call `pushChunk(streamIndex, array)` in a loop; when done, call `closeStream(streamIndex)`.
4. **Consumer task:** Call `consumeOutputStream(runIndex, onChunk, onDone, onError)`. The Host drives the output stream in an async task, yields periodically, and invokes the callbacks. Serialize or display results in JS (e.g. update the UI or trigger a download).

### File blocks in the graph UI

In the graph UI, **file blocks** are output-only nodes that hold a URL (e.g. a dropped file as a blob URL, or `indexeddb://projectId/nodeId` for persisted files). When a file block is connected to a computation or presentation input, the frontend builds a map from input name to stream index by calling `createStreamInput`, then **feeding** the stream in the worker so that parsing runs in WASM with back-pressure:

- **feedStreamFromUrl(streamIndex, url, format?)** — For fetchable URLs (`https:`, `data:`), the client sends the URL and optional format (`"numeric"` | `"csv"`). The worker fetches and runs **startFeeder** (newline-delimited) or **startCsvFeeder** (row-as-map) according to format. Parsing and send happen in the worker with back-pressure.
- **feedStreamFromReadableStream(streamIndex, stream, format?)** — For blob or IndexedDB-backed files, the client resolves the URL to a `ReadableStream` (e.g. `blob.stream()`), then sends the stream (and optional format) to the worker (transferable); the worker runs **startFeeder** or **startCsvFeeder** on it.

So the client sends **only the URL or the stream**; the worker fetches/reads and parses. For URLs that cannot be fetched by the worker (e.g. `indexeddb://` when the client must read from IDB), the client gets a `ReadableStream` from the blob and uses **feedStreamFromReadableStream**. Fallback: when `blob.stream` is not available, the client fetches/reads, parses in JS, and calls `pushChunk` / `closeStream`.

## CLI

The native CLI can run expressions that use `$name` by binding stream names to files.

### Usage

```text
snaq-lite [--numeric] [--stream-variance zero|infer] [--stream name=path ...] <expression>
```

- **--stream name=path** (or **-s name=path**): Bind the stream `$name` to the file at `path`. Repeat for multiple streams (e.g. `--stream a=1.txt --stream b=2.txt`).
- **--stream-variance zero|infer**: How to assign variance (uncertainty) to numbers read from stream files. **zero** (default): treat all numbers as exact (variance 0). **infer**: infer variance from the number of decimal places in the **text** (same rule as language literals: no decimal point → ±0.5; N decimal places → ±5×10^−(N+1)). Important for scientific work where reported precision (e.g. `10.50` vs `10.5`) should propagate as uncertainty. **Infer applies only to text-based sources** (CSV cells, newline-delimited lines); Parquet and Arrow always use zero variance (binary formats have no “decimal places expressed”).
- **--numeric** / **-n**: Same as without streams; for vector results, each element is printed on its own line.
- Each `$name` in the expression must have a corresponding `--stream name=path`; otherwise the runtime returns **unbound stream input: name**.

### File formats

Format is detected from the file path (extension, and optionally magic bytes for extension-less files):

- **CSV** (`.csv`): First row = column headers; each following row becomes one stream element as a **map** (e.g. `{ x: 1, y: 2 }`). Cells are parsed as numbers; empty cells → undefined. Use e.g. `$data.map(fn r => (r.column_name))` to extract a column.
- **Parquet** (`.parquet`, or magic `PAR1`): Row-as-map semantics; each row is one stream element. **Requires building the CLI with the `parquet` feature** (e.g. `cargo build --features parquet`). Parsing streams row-by-row (record-batch-sized internal buffering only). Column values: numeric types → numeric; null → undefined; other types (e.g. string) → undefined.
- **Arrow IPC** (`.arrow`, `.ipc`, or magic `ARROW1`): Same row-as-map semantics as Parquet. Also requires the `parquet` feature. Supports both IPC file format (with footer) and IPC stream format (sequential). Same column policy: numeric → numeric, null → undefined, unsupported type → undefined.
- **Other** (e.g. no extension, `.txt`): Treated as **newline-delimited numbers**: one numeric value per line. Empty lines are skipped. Invalid lines (non-numeric) yield a stream error.

Tabular files (CSV, and Parquet/Arrow when the feature is enabled) yield a stream of maps; the language can index by column with `row.col` or `row["col"]`. The parser trait (**TabularParser**) is implemented for each format so new formats (e.g. NDJSON, Excel) can be added by implementing it and extending format detection.

**Map streams and arithmetic:** Arithmetic or comparison with map values (e.g. `$x * 10` or `sin($x)` when `$x` is a CSV stream) is not supported and returns a runtime error. Use `$x.map(fn r => (r.column_name))` to get a numeric stream first, then apply arithmetic or functions.

### Example (numeric lines)

With a file `numbers.txt` containing:

```text
1
2
3
```

running:

```text
snaq-lite --stream data=numbers.txt '$data * 2'
```

prints the evaluated stream as a vector: `[2, 4, 6]`.

With `--numeric`, the same command prints one value per line:

```text
2
4
6
```

With **--stream-variance infer**, numeric values from text (CSV cells or newline-delimited lines) get variance from decimal places (e.g. `10.5` → larger variance than `10.50`). Example:

```text
snaq-lite --stream-variance infer --stream d=data.csv '$d.map(fn r => (r.x))'
```

### Example (CSV tabular)

With a file `data.csv` containing:

```text
x,y
1,2
3,4
```

running:

```text
snaq-lite --stream d=data.csv '$d.map(fn r => (r.x))'
```

prints `[1, 3]` (column `x` from each row).

### Output

When the result is a vector (e.g. `$data * 2`), the CLI consumes the stream and prints it as `[e1, e2, ...]` (or, with `--numeric`, one element per line). When the result is not a vector (e.g. a scalar expression that does not use streams), the single value is formatted and printed.

### Limits and edge cases (CLI)

- **Invalid --stream-variance:** The value must be **zero** or **infer** (case-insensitive). Any other value (e.g. `--stream-variance exact`) causes the CLI to exit with **error: --stream-variance must be zero or infer, got "…"**. The option is global (applies to all streams in the run).
- **Duplicate stream name:** If you pass the same name twice (e.g. `--stream x=a.txt --stream x=b.txt`), the CLI exits with **duplicate stream name: x**.
- **File not found:** If a file at `path` cannot be opened, the feeder thread logs to stderr and closes the sender; that stream yields no data, so the pipeline may produce an empty or partial result. The run does not fail; check stderr for I/O errors.
- **Invalid line (numeric files):** A non-numeric line in a newline-delimited numeric file yields a stream error; the run fails and the CLI prints the error.
- **Invalid cell (CSV):** A non-numeric cell in a CSV row yields a stream error (one `Err` element in the stream); the run fails and the CLI prints the error.
- **Feeder thread panic:** If a feeder thread panics (e.g. bug in the feeder), the main thread reports **stream feeder thread panicked** and exits with code 1 after consumption finishes.

## Summary

- **`$name`** — external stream reference; resolved from the Host’s stream input registry.
- **Chunks** — batches of elements (Ok(Some(value)), Ok(None), or Err) pushed by the Host.
- **Registry** — maps names to stream handle ids; the actual receiver is registered separately and consumed when the stream is driven.
- **Host** — creates channel, registers receiver, sets stream input map, runs with **run_with_stream_inputs**, then consumes the vector stream while pushing chunks and closing the sender for EOF.
- **Tabular (CLI):** CSV files (by extension) are parsed as rows; each row is one stream element as a map. Parquet and Arrow IPC are supported when the CLI is built with the `parquet` feature; parsing is row-by-row (no full-file materialization of rows). In WASM, the host can parse in JS and push row-shaped chunks via `pushChunk` with map values.
