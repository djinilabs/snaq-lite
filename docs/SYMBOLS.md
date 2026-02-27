# Symbols and symbolic evaluation

This document describes how symbolic constants and unknown identifiers work, and how symbolic evaluation differs from numeric evaluation. It does not describe internal representation or substitution algorithms.

## Built-in symbols

The language provides these **symbolic constants** by name:

- **`pi`** and **`π`** (Unicode) — the mathematical constant π.
- **`e`** — the base of the natural logarithm.
- **`phi`** — the golden ratio φ.
- **Physical constants** (dimensionless numeric values; combine with units for dimensional expressions): **`c`** (speed of light, 299792458 m/s in SI), **`h`** (Planck constant), **`hbar`** (ℏ = h/(2π)), **`R`** (gas constant, J/(mol·K)). Example: `c * m / s` gives the speed of light in m/s.

These have numeric values when you request a numeric result (e.g. via `run_numeric`). When you do not substitute, expressions keep them in symbolic form (e.g. `1 + π`, `2 * pi * rad`).

Additional constants (e.g. √2, √3) may appear in **exact** symbolic results for certain built-in functions (e.g. trig at well-known angles). They are part of the symbolic result and can be substituted numerically when using `run_numeric`.

## Unknown identifiers

Any identifier that is **not**:

- a variable bound in the current scope,
- a registered unit,
- or a keyword,

is treated as a **symbol**. Examples: `x`, `alpha`, `speed` when not bound and not a unit.

- In **symbolic evaluation** (default `run`): the expression is kept with the symbol (e.g. `1 + x`, `2 * speed`).
- In **numeric evaluation** (`run_numeric`): the runtime tries to **substitute** the symbol. If the symbol has a value in the symbol registry, it is replaced; if it is bound in the program (variable), the binding is used. If a symbol has no value and is not bound, the runtime returns an error: **symbol has no value**.

So: use symbols when you want to keep expressions in symbolic form; use variables when you want to bind a value in the program; use `run_numeric` when you want a single numeric quantity and all symbols (and unbound identifiers used as units) must be resolvable.

## Resolution order

When the language resolves a **bare identifier** (e.g. `x`, `m`, `pi`), it uses this order:

1. **Scope (variables)** — If the name is bound in the current block or an outer block, the identifier evaluates to that value. Variables **shadow** unit names and symbols.
2. **Unit registry** — If the name is a registered unit (or prefix+unit), the identifier is treated as **1** in that unit.
3. **Symbol** — Otherwise the identifier is treated as a **symbol** (e.g. `pi`, `e`, or any unknown name).

Example: `DEF = 3; DEF + 2` → **5**, because `DEF` is bound to 3 in scope, so it is not interpreted as the unit decafarad (da·F).

## Symbolic vs numeric evaluation

| Mode | Typical use | Result |
|------|-------------|--------|
| **Symbolic** (e.g. `run`) | Keep π, unknowns, or exact forms in the result | Value can be Numeric, Symbolic, FuzzyBool, Vector, or Undefined. Display shows expressions like `1 + π` or `√2/2`. |
| **Numeric** (`run_numeric`) | Get a single number (with optional unit) | All symbols and unbound unit-like identifiers are substituted; result is a quantity. Errors if result is not numeric (e.g. comparison, vector, undefined) or if a symbol has no value. |

**Use cases:**

- **Symbolic:** Documenting formulas, teaching, or passing expressions to another system.
- **Numeric:** Computation, display of a single number, or when you have provided values for all symbols (via the symbol registry or variable bindings in the program).

When a symbol has **no value** (not in the symbol registry and not bound) and you call `run_numeric`, the runtime returns an error: **symbol has no value** (see [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md)).

## See also

- [SYNTAX.md](SYNTAX.md) — identifiers and keywords
- [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) — how bindings affect scope
- [UNITS_AND_QUANTITIES.md](UNITS_AND_QUANTITIES.md) — unit resolution
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — SymbolHasNoValue and related errors
- [README.md](README.md) — language overview and index
