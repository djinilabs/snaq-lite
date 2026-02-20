# snaq-lite

[![Tests](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml/badge.svg)](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml)

A Rust-based reactive arithmetic language that runs natively or from WebAssembly. Expressions form a computation graph: when an argument changes, only dependent operations are recomputed (via [Salsa](https://github.com/salsa-rs/salsa)).

**API:**

- **`run(expression)`** — Parse and evaluate; returns `Result<Value, RunError>`. By default the result is **symbolic** (e.g. `1 + pi` → `1 + π`). `Value` is either `Numeric(Quantity)` or `Symbolic(SymbolicQuantity)`; display with `.to_string()` or substitute with `value.to_quantity(&symbol_registry)`.
- **`run_numeric(expression)`** — Like `run`, but substitutes all symbols (pi, π, e, etc.) and returns `Result<Quantity, RunError>`. Use when you need a single numeric quantity. Errors with `SymbolHasNoValue` if a symbol has no defined value.
- **`run_scalar(expression)`** — Same as `run_numeric`, but returns `Result<f64, RunError>`; errors if the result is not dimensionless.

**Language:** Float literals, `+`, `-`, `*`, `/` or `per`, parentheses, **implicit multiplication** (e.g. `10 20` → 200, `2 (3+4)` → 14), **quantity literals** (`100 m`, bare unit like `hour`), and **symbols** (`pi`, `π`, `e`, or any unknown identifier). Unknown identifiers are treated as symbols (not units). Built-in units: all 7 SI base units, SI derived with special names, time/length (km, g, hour, minute, etc.), and Numbat-style (mile, parsec, au, light_year, eV, celsius). Multiplication and division bind tighter than addition and subtraction.

**Examples:** `1 + 2` → `3`; `1 + pi` → `1 + π` (symbolic) or use `run_numeric` for a number; `3 + 2 + pi + 1` → `6 + π`; `10 20` → `200`; `100 km / hour` → `100 km/hour`; `1.5 km + 500 m` → `2000 m`; `1 mile`, `1 volt`. Division by zero: nonzero/0 yields ±∞; 0/0 errors. **CLI:** `snaq-lite "1 + pi"` prints symbolic; `snaq-lite --numeric "1 + pi"` prints the numeric result.

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
