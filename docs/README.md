# snaq-lite language reference

snaq-lite is an expression-oriented language for arithmetic with **physical quantities**, **units**, **symbols**, **vectors**, and **maps**. You write expressions (and optionally variable bindings); the result of a program is the value of the **last** expression.

## What the language supports

- **Numbers and quantities** — Float literals, optional units (e.g. `100 m`, `2 pi rad`), unit conversion with `as`, and division alias `per`.
- **Symbols** — Built-in constants like `pi` and `e`; unknown identifiers stay symbolic until you ask for a numeric result.
- **Vectors** — Literals `[ ... ]`, transpose `'`, and operations with scalars or other vectors (element-wise, outer product, dot product).
- **Maps** — Literals `{ key: value, ... }` with unquoted keys; access via `.key` or `[key]` (bracket content trimmed); missing key → undefined. See [MAPS.md](MAPS.md).
- **Dates** — Temporal literals `@YYYY`, `@YYYY-MM-DD`, etc.; Date ± Time (grain rule), Date − Date → duration; comparison yields true/false/uncertain by interval overlap. See [DATES.md](DATES.md).
- **Comparisons** — `==`, `!=`, `<`, `<=`, `>`, `>=`; same dimension required; result is a boolean-like value (true, false, or uncertain when operands have variance).
- **Conditionals** — `if condition then expression else expression`; condition can be uncertain (superposition of both branches).
- **Functions** — Built-ins: `sin`, `cos`, `tan` (angle argument), `sqrt` (non-negative), `max`, `min` (two same-dimension arguments). Vectors support methods such as `.sum()`, `.mean()`, `.min()`, `.max()`, `.dot(other)`, `.norm()`, `.product()`, `.variance()`, `.stddev()`, `.all()`, `.any()` (see [VECTORS.md](VECTORS.md)).
- **Precision** — Implicit from decimal places in literals, or explicit with `value ~ error`.
- **Variables** — Immutable bindings (`name = expression`) with lexical scope; result can be the last binding’s value.
- **External streams** — `$name` refers to a stream supplied by the Host; see [EXTERNAL_STREAMS.md](EXTERNAL_STREAMS.md).
- **Computation block inputs (visual graph)** — In the canvas app, declare input ports with `input name: Type` at the top of a block (e.g. `input x: Vector`); input handles appear and you can connect other blocks. See [COMPUTATION_BLOCKS.md](COMPUTATION_BLOCKS.md).

Programs are **expression lists**: multiple expressions separated by newlines or `;`, optionally inside blocks `{ ... }`. The **result** is the last expression’s value (or the last binding’s right-hand side, or undefined if the list is empty).

## Table of contents

| Topic | Document |
|-------|----------|
| **Syntax** — Tokens, precedence, implicit multiplication, keywords | [SYNTAX.md](SYNTAX.md) |
| **Literals and value types** — Numbers, vectors, numeric vs symbolic vs boolean vs undefined | [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) |
| **Units and quantities** — Quantity literals, unit expressions, conversion, prefixes, supported units | [UNITS_AND_QUANTITIES.md](UNITS_AND_QUANTITIES.md) |
| **Symbols** — Built-in symbols, unknown identifiers, symbolic vs numeric evaluation | [SYMBOLS.md](SYMBOLS.md) |
| **Comparisons and FuzzyBool** — Comparison operators, true/false/uncertain, vector comparisons | [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md) |
| **Vectors** — Literals, transpose, orientation, vector–scalar and vector–vector operations | [VECTORS.md](VECTORS.md) |
| **Maps** — Map literals, dot and bracket access, missing key → undefined | [MAPS.md](MAPS.md) |
| **Dates** — Temporal literals, grain, Date ± Time, Date − Date, comparison | [DATES.md](DATES.md) |
| **Functions** — Call syntax, built-ins (sin, cos, tan, max, min), arity and dimensions | [FUNCTIONS.md](FUNCTIONS.md) |
| **Precision** — Implicit (decimal places) and explicit (`value ~ error`) | [PRECISION.md](PRECISION.md) |
| **Errors and edge cases** — When things go wrong, division by zero, undefined, binding limits | [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) |
| **Blocks and expressions** — Multiple expressions, blocks, result = last value, undefined | [BLOCKS_AND_EXPRESSIONS.md](BLOCKS_AND_EXPRESSIONS.md) |
| **Variable bindings** — Assignments, scope, shadowing, chained assignment | [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) |
| **Conditionals** — if/then/else, FuzzyBool, superposition | [CONDITIONALS.md](CONDITIONALS.md) |
| **External streams** — `$name`, chunk format, Host workflow | [EXTERNAL_STREAMS.md](EXTERNAL_STREAMS.md) |
| **Computation blocks** — Input parameters, wiring, `input name: Type` | [COMPUTATION_BLOCKS.md](COMPUTATION_BLOCKS.md) |

Other: [NUMBAT_COMPARISON.md](NUMBAT_COMPARISON.md) — comparison with Numbat (implementation-oriented).
