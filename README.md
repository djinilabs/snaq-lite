# snaq-lite

[![Tests](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml/badge.svg)](https://github.com/djinilabs/snaq-lite/actions/workflows/test.yml)

**snaq-lite** is a reactive arithmetic language for quantities, units, and uncertainty. Expressions form a computation graph: when an argument changes, only dependent operations are recomputed (via [Salsa](https://github.com/salsa-rs/salsa)). It runs natively in Rust or from WebAssembly.

The language combines **numeric quantities with units** (SI and common derivatives), **symbolic math** (e.g. keep π in expressions or substitute for numbers), **uncertainty** (implicit from decimal places or explicit with `~`), and **statistical comparisons** that yield crisp or uncertain booleans. You can write **variable bindings**, **blocks**, **vectors**, and **conditionals** (`if … then … else`), and call built-ins like `sin`, `cos`, `tan`, `max`, and `min`. By default evaluation is symbolic; use `run_numeric()` when you want a single numeric result.

---

## Language at a glance

- **Quantities and units** — Literals like `100 m`, `1 km/hour`, `2 pi rad`; unit conversion with `as` (e.g. `10 km as m`). SI base and derived units, time, angle, area, and Numbat-style units (mile, parsec, eV, etc.); plural names accepted (e.g. meters → meter).
- **Numbers and precision** — Values carry mean and variance. Implicit variance from decimal places (e.g. `10.5`); explicit error with `value ~ error` (e.g. `10 ~ 2`).
- **Symbols** — Unknown identifiers are symbols (`pi`, `π`, `e` or custom). Default evaluation keeps them symbolic; substitute via `run_numeric()` or a symbol registry.
- **Comparisons** — `==`, `!=`, `<`, `<=`, `>`, `>=` (same dimension). Result is a **FuzzyBool**: `true`, `false`, or `uncertain(prob)` when variance matters. Vectors: element-wise, outer, or row×column reduction.
- **Variables and blocks** — Immutable bindings `name = expression`; blocks `{ ... }` with multiple expressions (newline or `;`). Result = last expression (or last binding’s RHS). See [docs/VARIABLE_BINDINGS.md](docs/VARIABLE_BINDINGS.md) and [docs/BLOCKS_AND_EXPRESSIONS.md](docs/BLOCKS_AND_EXPRESSIONS.md).
- **Conditionals** — `if condition then expr else expr`; condition must be FuzzyBool. Crisp true/false evaluate one branch; uncertain conditions blend both branches (numeric or symbolic).
- **Vectors** — Literals `[ expr, ... ]`, postfix transpose `'`. Vector×scalar maps; vector×vector by orientation (element-wise, outer, dot). Display as `[e1, e2, ...]`.
- **Functions** — Built-ins: `sin`, `cos`, `tan` (one argument, angle); `max`, `min` (two same-dimension args). You can define your own with `fn (params) => body` or `fn name(params) => body`; optional default parameters, block bodies, and closures. Positional and named arguments (e.g. `max(a: 1, b: 2)`). See [docs/FUNCTIONS.md](docs/FUNCTIONS.md).

---

## API

- **`run(expression)`** — Parse and evaluate; returns `Result<Value, RunError>`. Result is **symbolic** by default (e.g. `1 + pi` → `1 + π`). `Value` can be `Numeric(Quantity)`, `Symbolic(...)`, `FuzzyBool`, `Vector(...)`, `Function(...)`, or `Undefined`. Multiple expressions and blocks allowed; result is the last value (or `Undefined` if empty).
- **`run_numeric(expression)`** — Substitute symbols and return `Result<Quantity, RunError>`. Errors on missing symbol, comparison result, or undefined result.
- **`run_scalar(expression)`** — Like `run_numeric` but returns `Result<f64, RunError>`; errors if not dimensionless or undefined.

Use `run_with_registry(input, &UnitRegistry)` (and optional symbol registry) for custom units/symbols.

---

## Examples

| Input | Result (conceptually) |
|-------|------------------------|
| `1 + 2` | `3` |
| `x = 10` then `x + 1` | `11` |
| `{ a = 2; b = 3; a * b }` | `6` |
| `1 + pi` | `1 + π` (symbolic) or numeric with `run_numeric` |
| `100 km / hour` | `100 km/hour` |
| `10 km as m` | `10000 m` |
| `sin(pi rad)` | `0` |
| `1 < 2` | `true`; with variance, may be `uncertain(prob)` |
| `[1, 2, 3]` | vector `[1, 2, 3]` |
| `fn mysum(a, b) => (a + b)` then `mysum(1, 2)` | `3` |

**CLI:** `snaq-lite "1 + pi"` (symbolic); `snaq-lite --numeric "1 + pi"` (numeric).

---

## Structure

- **snaq-lite-lang** — Core library (parser, AST, eval). Platform-agnostic.
- **snaq-lite-cli** — Native CLI binary.
- **snaq-lite-wasm** — WASM build for the web.

---

## Run tests

- **All tests (native):** `cargo test --workspace`
- **Core library only:** `cargo test -p snaq-lite-lang`
- **With output:** `cargo test --workspace -- --nocapture`
- **WASM (Node):** `wasm-pack test --node crates/snaq-lite-wasm` (requires [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/) and Node)

---

## Build and run

- **Native CLI:** `cargo run -p snaq-lite-cli`
- **WASM:** `rustup target add wasm32-unknown-unknown`, install [wasm-pack](https://rustwasm.github.io/wasm-pack/installer/), then  
  `wasm-pack build crates/snaq-lite-wasm --target web` (output in `crates/snaq-lite-wasm/pkg/`)
