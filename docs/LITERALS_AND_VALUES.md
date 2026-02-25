# Literals and value types

This document describes the literal forms in the language and the kinds of values that expressions can produce. It does not describe implementation types.

## Numeric literals

- **Format:** Integer (`42`), decimal (`3.14`, `.5`), or with exponent (`1e-2`, `2.5E+3`).
- Values are parsed as floating-point numbers. Invalid numeric strings produce a parse error.

### Implicit precision (uncertainty)

Every numeric literal carries an **implicit uncertainty** derived from how it is written:

- **No decimal point** (e.g. `10`, `42`): the value is treated as having an absolute error of **±0.5** (so the implied range is 9.5–10.5 for `10`).
- **With decimal places** (e.g. `10.5`, `10.50`): the absolute error is **±5×10^−(N+1)** where N is the number of decimal places in the mantissa. So `10.5` has one decimal place → ±0.05; `10.50` has two → ±0.005.

This uncertainty is used for variance in subsequent arithmetic and for **statistical comparisons** (see [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md)). Explicit precision can be set with the `~` operator; see [PRECISION.md](PRECISION.md).

## Vector literals

- **Syntax:** `[ expr, expr, ... ]` or `[]`.
- Elements are arbitrary expressions, separated by commas. Nested vectors are allowed (e.g. `[[1,2],[3,4]]`).
- The value of a vector literal is a **vector** whose elements are the evaluated element expressions. See [VECTORS.md](VECTORS.md) for vector operations and semantics.

## Value types (what expressions produce)

When you evaluate a program or expression, the result is one of the following **value types**:

| Type | Description | When it arises |
|------|-------------|----------------|
| **Numeric** | A quantity: a number with optional unit and variance. | Literals with or without units, arithmetic on numeric operands, unit conversion, `run_numeric` substitution. |
| **Symbolic** | An expression that still contains symbols (e.g. π, or an unknown identifier). | When symbols are not substituted (e.g. `1 + pi`, `1 + x` with `x` unbound and not a unit). |
| **FuzzyBool** | A boolean-like result: `true`, `false`, or `uncertain(probability)`. | Comparison operators (`==`, `!=`, `<`, `<=`, `>`, `>=`) when operands have the same dimension. |
| **Vector** | A vector of values (possibly nested). | Vector literals, transpose, and vector–scalar or vector–vector operations. |
| **Undefined** | No value. | Empty program or empty block `{}`. |

### How results are used

- **`run(expression)`** returns a **Value** (one of the types above). Display (e.g. in a CLI) shows a string form: numbers with units, symbolic expressions like `1 + π`, `true`/`false`/`uncertain(…)`, vector as `[ ... ]`, or `undefined`.
- **`run_numeric(expression)`** substitutes all symbols and expects a **single numeric quantity**. If the result is not numeric (e.g. it is a comparison, a vector, or undefined), an error is returned. See [SYMBOLS.md](SYMBOLS.md) and [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md).
- **`run_scalar(expression)`** is like `run_numeric` but the result must be **dimensionless** (a plain number).

## See also

- [SYNTAX.md](SYNTAX.md) — literal token format
- [PRECISION.md](PRECISION.md) — explicit precision with `~`
- [UNITS_AND_QUANTITIES.md](UNITS_AND_QUANTITIES.md) — quantity literals with units
- [VECTORS.md](VECTORS.md) — vector semantics
- [README.md](README.md) — language overview and index
