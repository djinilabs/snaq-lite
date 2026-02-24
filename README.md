# snaq-lite

[![Tests](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml/badge.svg)](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml)

A Rust-based reactive arithmetic language that runs natively or from WebAssembly. Expressions form a computation graph: when an argument changes, only dependent operations are recomputed (via [Salsa](https://github.com/salsa-rs/salsa)).

**API:**

- **`run(expression)`** — Parse and evaluate; returns `Result<Value, RunError>`. By default the result is **symbolic** (e.g. `1 + pi` → `1 + π`). `Value` is `Numeric(Quantity)`, `Symbolic(SymbolicQuantity)`, `FuzzyBool` (comparison results: `true`, `false`, or `uncertain(prob)` when variance is significant), or `Vector(...)`; display with `.to_string()` or substitute with `value.to_quantity(&symbol_registry)` (errors for fuzzy boolean/vector).
- **`run_numeric(expression)`** — Like `run`, but substitutes all symbols and returns `Result<Quantity, RunError>`. Use when you need a single numeric quantity. Errors with `SymbolHasNoValue` if a symbol has no value, or `BooleanResult` if the expression is a comparison (e.g. `1 < 2`).
- **`run_scalar(expression)`** — Same as `run_numeric`, but returns `Result<f64, RunError>`; errors if the result is not dimensionless.

**Language:** Float literals, `+`, `-`, `*`, `/` or `per`, parentheses, **comparison operators** `==`, `!=`, `<`, `<=`, `>`, `>=` (same dimension required; result is **FuzzyBool**: `true`, `false`, or `uncertain(prob)` when operands have variance and the comparison is in the confidence band; with vectors: broadcast, element-wise, outer, or row×column reduce), **implicit multiplication** (e.g. `10 20` → 200, `2 (3+4)` → 14, `2 pi rad` or `pi rad` as one factor so constants and units chain without `*`), **quantity literals** (`100 m`, bare unit like `hour`), **unit conversion** with `as` (e.g. `10 km as m`, `10 km per hour as m / s`), **symbols** (`pi`, `π`, `e`, or any unknown identifier), and **function calls** with positional and optional named arguments. **Vector literals** `[ expr, ... ]` and postfix transpose `'` (e.g. `[1,2,3]'`). Unknown identifiers are treated as symbols (not units). **Built-in functions:** `sin`, `cos`, `tan` (one argument, angle in rad or degree); `max`, `min` (two arguments, same dimension). Example: `sin(pi * rad)` → 0, `sin(180 degree)` → 0, `max(3, 2)` → 3, `max(a: 1, b: 2)`. Built-in units: all 7 SI base units, SI derived with special names, time/length (km, g, hour, minute, meter, second, etc.), angle (rad, degree), **area** (m2, m², km2, cm2, mm2, are, hectare, ha, squaremeter, squareinch, in2, sqm, sqin, squarefoot, ft2, sqft; hectare = 100 ares, 1 are = 100 m²), length inch (in) and foot (ft), and Numbat-style (mile, parsec, au, light_year, eV, celsius). Plural unit names (e.g. meters, seconds, kilometers) are accepted and normalized to the canonical singular form. Multiplication and division bind tighter than addition and subtraction.

**Examples:** `1 + 2` → `3`; `1 < 2` → `true`, `1 == 2` → `false` (exact literals yield crisp true/false; numbers with variance can yield `uncertain(prob)`); `100 m < 1 kilometer` → `true`; `[1, 2, 3]` → vector; `[1, 2, 3]'` → same vector (transpose); `1 + pi` → `1 + π` (symbolic) or use `run_numeric` for a number; `3 + 2 + pi + 1` → `6 + π`; `10 20` → `200`; `100 km / hour` → `100 km/hour`; `10 km as m` → `10000 m`; `10 km per hour as m / s` → speed in m/s; `1.5 km + 500 m` → `2000 m`; `2 pi rad`, `pi rad` (implicit mul: constant · unit); `1 mile`, `1 volt`; `sin(pi * rad)` → 0, `sin(pi rad)` → 0, `sin(180 degree)` → 0, `max(3, 2)` → 3. Division by zero: nonzero/0 yields ±∞; 0/0 errors. **CLI:** `snaq-lite "1 + pi"` prints symbolic; `snaq-lite --numeric "1 + pi"` prints the numeric result.

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
