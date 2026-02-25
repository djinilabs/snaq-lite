# Precision

This document describes how numeric precision (uncertainty) is represented: implicitly from literal form and explicitly with the `~` operator. It does not describe variance propagation formulas or internal representation.

## Implicit precision (from decimal places)

Every **numeric literal** gets an implicit uncertainty based on how it is written:

- **No decimal point** (e.g. `10`, `42`): absolute error **±0.5** (so 10 means “between 9.5 and 10.5”).
- **With decimal places** (e.g. `10.5`, `10.50`): absolute error **±5×10^−(N+1)** where N is the number of decimal places in the mantissa. So:
  - `10.5` (one decimal place) → ±0.05
  - `10.50` (two decimal places) → ±0.005

This uncertainty is carried as variance through arithmetic and affects **statistical comparisons** (see [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md)). More detail is in [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md).

## Explicit precision: value ~ error

**Syntax:** `left ~ right`

- **Left:** Expression whose value is the **central value** (mean) of the result.
- **Right:** Expression whose **value** (only) is used as the **error** (half-width or standard deviation, depending on how the language models it). The variance of the result is derived from this error (e.g. variance = error²). The **variance** of the right-hand side is **discarded**; only its central value matters.
- **Precedence:** `~` binds **tighter** than `*` and `/`, so e.g. `5 + 10 ~ 2` is parsed as `5 + (10 ~ 2)` (result: 5 plus a quantity with mean 10 and error 2).

**Requirements:**

- **Both sides must be numeric.** If either side is symbolic, boolean, or vector, the runtime returns an error: **both sides of ~ must be numeric**.
- **Right-hand side must be strictly positive.** If the right-hand side is ≤ 0 or non-finite, the runtime returns an error: **precision must be strictly positive**.

**Example:** `10 ~ 2` gives a quantity with mean 10 and uncertainty corresponding to error 2 (e.g. variance 4). Useful when you want to attach an explicit error to a value instead of relying on decimal places.

## See also

- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — implicit precision of literals
- [SYNTAX.md](SYNTAX.md) — precedence of `~`
- [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md) — how uncertainty affects comparisons
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — TildeRequiresNumeric, PrecisionMustBePositive
- [README.md](README.md) — language overview and index
