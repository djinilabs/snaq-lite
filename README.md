# snaq-lite

[![Tests](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml/badge.svg)](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml)

A Rust-based reactive arithmetic language that runs natively or from WebAssembly. Expressions form a computation graph: when an argument changes, only dependent operations are recomputed (via [Salsa](https://github.com/salsa-rs/salsa)).

**API:** `run(expression)` — parse the expression (e.g. `"1 + 2"` or `"1.5 * (10 - 3)"`), evaluate, return `Result<f64, RunError>`. Language: float literals (conventional syntax), `+`, `-`, `*`, `/`, and parentheses; no bindings. Multiplication and division bind tighter than addition and subtraction.

## Structure

- **snaq-lite-lang** – Core library (parser, AST, eval). Platform-agnostic.
- **snaq-lite-cli** – Native CLI binary.
- **snaq-lite-wasm** – WASM build for the web.

## Run tests

- **All tests (native):** `cargo test --workspace`
- **Core library only:** `cargo test -p snaq-lite-lang`
- **With output:** `cargo test --workspace -- --nocapture`
- **WASM build (generation only):** `cargo build -p snaq-lite-wasm --target wasm32-unknown-unknown`, or `./scripts/check-wasm-build.sh`
- **WASM runtime (Node):** `wasm-pack test --node crates/snaq-lite-wasm` (requires [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/) and Node). Optional: `--headless --firefox` or `--chrome` for browser.

## Build and run

- **Native CLI:** `cargo run -p snaq-lite-cli`
- **WASM:** Install the target and wasm-pack, then:
  - `rustup target add wasm32-unknown-unknown`
  - Install [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/)
  - `wasm-pack build crates/snaq-lite-wasm --target web` (output in `crates/snaq-lite-wasm/pkg/`)
