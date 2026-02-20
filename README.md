# snaq-lite

[![Tests](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml/badge.svg)](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml)

A Rust-based reactive arithmetic language that runs natively or from WebAssembly. Expressions form a computation graph: when an argument changes, only dependent operations are recomputed (via [Salsa](https://github.com/salsa-rs/salsa)).

**API:**

- **`run(expression)`** — Parse, evaluate, and return `Result<Quantity, RunError>`. A `Quantity` has a numeric value and a unit (e.g. `2.5 m`, `100 km/hour`, or plain `3` for dimensionless).
- **`run_scalar(expression)`** — Same as `run`, but returns `Result<f64, RunError>`; errors if the result is not dimensionless (use when you only need a number).

**Language:** Float literals (conventional syntax), `+`, `-`, `*`, `/` or `per`, parentheses, **implicit multiplication** (e.g. `10 20` → 200, `2 (3+4)` → 14), and **quantity literals**: `100 m`, `1.5 * km`, or a bare unit like `hour`. Built-in units: **all 7 SI base units** (m, kg, s, A, K, mol, cd), **all SI derived units with special names** (J, C, V, F, ohm, S, Wb, T, H, Hz, N, Pa, W, lm, lx, Bq, Gy, Sv, kat), time/length (km, g, hour, minute, second, seconds), and Numbat-style (mile, parsec, au, light_year, eV, celsius). Multiplication and division bind tighter than addition and subtraction.

**Examples:** `1 + 2` → `3`; `10 20` → `200` (implicit mul); `2 (3+4)` → `14`; `100 km / hour` → `100 km/hour`; `3 kilometers per hour` → `3 km/hour`; `1.5 km + 500 m` → `2000 m`; `1 mile`, `1 eV`, `1 second`, `1 volt`.

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
