# Functions

This document describes how to call functions and what the built-in functions do. It does not describe how functions are dispatched or evaluated internally.

## Call syntax

- **Form:** `name ( arg1, arg2, ... )` — the identifier must be immediately followed by `(` so the parser treats it as a function call (see [SYNTAX.md](SYNTAX.md)).
- **Arguments:** Each argument can be:
  - **Positional:** an expression (e.g. `sin(pi rad)`, `max(3, 2)`).
  - **Named:** `name : expression` (e.g. `max(a: 1, b: 2)`).

Positional and named arguments can be mixed. The language binds positional arguments first, then named arguments (which can override or fill in parameters by name).

## Built-in functions

### Trigonometric: sin, cos, tan

- **Arity:** One argument.
- **Argument:** Must have **angle** dimension (e.g. in radians or degrees). The value is converted to radians internally for computation.
- **Result:** Dimensionless number (or symbolic expression for exact well-known angles). Variance is propagated when the argument has uncertainty.

**Well-known angles:** At certain angles (e.g. 0, π/6, π/4, π/3, π/2, π in radians, or 0°, 30°, 45°, 60°, 90°, 180° in degrees), the result may be returned in **exact symbolic form** (e.g. √2/2, √3/2) when the result is kept symbolic. When you request a numeric result, these are substituted to numbers.

**Errors:**

- **Unknown function** — if the name is not a built-in.
- **Expected angle** — if the argument is not an angle (e.g. `sin(1 m)` or `sin(1)` without a unit). For a dimensionless argument, the error message may suggest adding the `rad` unit (e.g. `sin(pi * rad)`).
- **Wrong arity** — e.g. `sin(1, 2)`.

### max, min

- **Arity:** Two arguments.
- **Arguments:** Must have the **same dimension** (e.g. two lengths, two times, two dimensionless numbers). Unit conversion is applied if needed.
- **Result:** The maximum or minimum of the two values, in the same dimension. If one or both arguments are symbolic, the result may be symbolic.

**Errors:**

- **Unknown function** — if the name is not a built-in.
- **Dimension mismatch** — if the two arguments have different dimensions (e.g. `max(1 m, 2 s)`).
- **Wrong arity** — e.g. `max(1)`.

## Use cases and edge cases

- **Trig with units:** Prefer angle units so the argument is clearly an angle: `sin(pi rad)`, `sin(180 degree)`. Avoid `sin(pi)` without a unit when you mean radians; the runtime may report expected angle (dimensionless).
- **Named arguments:** Useful for clarity, e.g. `max(a: 3, b: 2)` or mixing: `max(3, b: 2)`.
- **Vector arguments:** Unary functions (sin, cos, tan) accept a **vector** of angles and apply **element-wise**; the result is a vector. For max/min with one vector and one scalar, or two vectors, behaviour is as defined by the language (element-wise or reduction as for other binary operations; see [VECTORS.md](VECTORS.md) if applicable).

## See also

- [SYNTAX.md](SYNTAX.md) — identifiers and function call tokenization
- [UNITS_AND_QUANTITIES.md](UNITS_AND_QUANTITIES.md) — angle units (rad, degree)
- [VECTORS.md](VECTORS.md) — functions applied to vectors
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — unknown function, expected angle, dimension mismatch
- [README.md](README.md) — language overview and index
