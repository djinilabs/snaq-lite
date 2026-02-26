# External data as streams

Programs can refer to **external stream inputs** using the `$name` syntax. The Host supplies data by pushing **chunks** into a channel and registering the stream handle under that name. Evaluation returns a **pipeline** (a vector description); the Host then consumes the resulting stream while pushing data.

## Syntax: `$name`

- **Syntax:** `$` followed by an identifier (e.g. `$sales_data`, `$readings`).
- **Meaning:** The expression denotes an external stream identified by `name`. The name is looked up in a **stream input registry** provided by the Host at run time. The registry maps names to **stream handles**, not to the data itself.
- **Use in expressions:** You can use `$name` anywhere a vector is valid. For example: `$sales_data * 2`, `$readings.sum()`, `take($log, 0, 100)`.

If the Host runs a program that uses `$name` but does **not** set the stream input registry (or does not register that name), evaluation fails with **unbound stream input: name**.

## Chunk format

The Host pushes data in **chunks**. Each chunk is a list of elements in the runtime’s value format:

- Each element is one of: `Ok(Some(value))` for a normal value, `Ok(None)` for a missing/undefined element, or `Err(run_error)` for an error.
- A chunk is a vector of such elements (e.g. up to 10,000 rows at a time). The Host is responsible for chunk size and I/O (e.g. reading Parquet or CSV in batches and converting to this format).

**End of stream:** The Host signals end-of-stream by closing/dropping the sender (or equivalent). The runtime then treats the stream as complete.

## Host workflow

1. **Create a channel** (e.g. an unbounded sender/receiver pair) whose items are **chunks** in the format above.
2. **Register the receiver:** Call the library’s **register** function with the receiver; it returns a **stream handle id**. The receiver is single-consumer: it is taken by the runtime when the stream is driven.
3. **Build the stream input map:** Map each name used in the program (e.g. `"sales_data"`) to the corresponding stream handle id.
4. **Run with stream inputs:** Call **run_with_stream_inputs**(input, unit_registry, stream_input_map). You get back the evaluated **Value** and the **database**. If the result is a vector (e.g. `$sales_data * 2`), it is a pipeline that reads from the registered stream.
5. **Consume the stream:** If the result is a vector, call **vector_into_stream** with the database and the vector’s inner pipeline. This returns a stream that yields elements (or errors). Drive this stream (e.g. in an async loop) while, in parallel, pushing chunks on the sender from your I/O (files, network, etc.). When you have no more data, close the sender to signal EOF.
6. **Edge cases:** Programs that use only external streams (e.g. root is `$x * 2`) do not produce a single numeric quantity; operations like **run_numeric** are not applicable for such programs. Use **run_with_stream_inputs** and then consume the vector stream as above.

## Limits and platform

- **run_numeric / to_quantity:** When the program result is a vector from an external stream (e.g. `$x * 2`), the result is a pipeline, not a single quantity. Requesting a numeric result for such a program is not supported; use **run_with_stream_inputs** and consume the vector stream instead.
- **Stream handle is single-consumer:** Each registered receiver is taken by the runtime when you call **vector_into_stream** on a pipeline that uses that input. Calling **vector_into_stream** again on the same pipeline (or another expression that uses the same `$name`) will not see the data again; the stream yields one error (**stream input not available (already consumed or not registered)**) then completes.
- **WASM:** The stream handle registry is thread-local. On WASM, drive the stream in an async task (e.g. with `wasm-bindgen-futures` or your async runtime) so that the main thread is not blocked. Chunked push and consumption work the same as on native targets.

## Summary

- **`$name`** — external stream reference; resolved from the Host’s stream input registry.
- **Chunks** — batches of elements (Ok(Some(value)), Ok(None), or Err) pushed by the Host.
- **Registry** — maps names to stream handle ids; the actual receiver is registered separately and consumed when the stream is driven.
- **Host** — creates channel, registers receiver, sets stream input map, runs with **run_with_stream_inputs**, then consumes the vector stream while pushing chunks and closing the sender for EOF.
