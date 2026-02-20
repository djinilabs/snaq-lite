# snaq-lite

A Rust-based reactive arithmetic language that runs natively or from WebAssembly. Expressions form a computation graph: when an argument changes, only dependent operations are recomputed (via [Salsa](https://github.com/salsa-rs/salsa)).

**API:** `run(expression)` — parse the expression (e.g. `"1 + 2"` or `"(10 - 3) + 1"`), evaluate, return `Result<i64, RunError>`. Language: integer literals and `+` / `-` with parentheses; no bindings.

## Structure

- **snaq-lite-lang** – Core library (parser, AST, eval). Platform-agnostic.
- **snaq-lite-cli** – Native CLI binary.
- **snaq-lite-wasm** – WASM build for the web.

## Run tests

- **All tests:** `cargo test --workspace`
- **Core library only:** `cargo test -p snaq-lite-lang`
- **With output:** `cargo test --workspace -- --nocapture`

## Build and run

- **Native CLI:** `cargo run -p snaq-lite-cli`
- **WASM:** Install the target and wasm-pack, then:
  - `rustup target add wasm32-unknown-unknown`
  - Install [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/)
  - `wasm-pack build crates/snaq-lite-wasm --target web` (output in `crates/snaq-lite-wasm/pkg/`)
