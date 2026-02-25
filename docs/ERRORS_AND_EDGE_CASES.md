# Errors and edge cases

This document lists the main error conditions and edge cases you may encounter when writing expressions. It does not reference internal error types or code.

## Parse errors

- **Invalid literal:** A numeric token that cannot be parsed as a float (e.g. malformed exponent or invalid character sequence) produces a parse error.
- **Invalid syntax:** Expressions that do not match the grammar produce a parse error. Examples: `2 3 m` (implicit multiplication not allowed between these tokens), unmatched brackets, or invalid use of keywords.

## Runtime errors (when they occur)

| Situation | What you see (summary) |
|-----------|------------------------|
| **Unknown unit** | An identifier was used as a unit but is not in the unit registry. |
| **Dimension mismatch** | Two values that must have the same dimension do not (e.g. `1 m + 1 s`, or converting to an incompatible unit with `as`). |
| **Division by zero** | Division where the divisor is zero. See below for nonzero/0 vs 0/0. |
| **Symbol has no value** | You requested a numeric result (`run_numeric`) but a symbol (or unbound identifier) has no value in the symbol registry and is not bound in the program. |
| **Unknown function** | The call uses a name that is not a built-in function. |
| **Expected angle** | A trig function (sin, cos, tan) received an argument that is not an angle (e.g. length or dimensionless number without unit). The message may suggest adding `rad` (e.g. `sin(pi * rad)`). |
| **Operation not supported for vector** | An operation that expects a scalar was given a vector (e.g. converting the result to a single quantity when the result is a vector). |
| **Transpose requires a vector** | The postfix `'` was applied to a non-vector (e.g. a scalar or symbolic expression). |
| **Vector length mismatch** | A vector operation (element-wise or similar) required two vectors of the same length; the lengths differed. |
| **Boolean result** | You requested a numeric quantity but the result is a comparison (true/false/uncertain). |
| **Expected condition** | The condition of `if ... then ... else ...` must evaluate to a boolean (true, false, or uncertain), not a number or symbolic expression. |
| **If branches type mismatch** | Both branches of `if ... then ... else ...` must be blendable (both numeric or both symbolic). You cannot mix e.g. number with vector or boolean. |
| **Both sides of ~ must be numeric** | The explicit-precision operator `~` was used with a symbolic, boolean, or vector operand. |
| **Precision must be strictly positive** | The right-hand side of `~` was ≤ 0 or non-finite. |
| **Result is undefined** | You requested a numeric quantity (or scalar) but the result is undefined (e.g. empty program or empty block). |
| **Binding value not supported** | You tried to bind a symbolic or vector value to a variable; only numeric, FuzzyBool, or undefined can be bound in the current version. |

## Division by zero

- **Nonzero / 0:** The result is **plus or minus infinity** (sign of the numerator). Infinity propagates through arithmetic and unit conversion (same dimension; only the unit may change).
- **0 / 0:** The runtime returns an error: **division by zero** (indeterminate).

There is **no NaN** in the language; only +∞ and −∞ for infinite values.

## Undefined result

- **When:** The program or block has **no** expressions, or the only expressions are bindings and the result is taken from an empty list (e.g. empty block `{}`, or empty input).
- **Value:** The result is **undefined**. Display shows something like `"undefined"`.
- **Conversion:** If you request a numeric quantity (e.g. `run_numeric("")` or `run_numeric("{}")`), the runtime returns an error: **result is undefined**.

## Binding limits

- **Allowed:** Binding a **numeric** value, a **FuzzyBool** (true/false/uncertain), or **undefined** to a variable.
- **Not allowed (current):** Binding a **symbolic** or **vector** value. The runtime returns an error: **binding value not supported** (or similar message).

See [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) for scope and shadowing.

## See also

- [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) — binding limits
- [BLOCKS_AND_EXPRESSIONS.md](BLOCKS_AND_EXPRESSIONS.md) — undefined and empty blocks
- [PRECISION.md](PRECISION.md) — requirements for `~`
- [CONDITIONALS.md](CONDITIONALS.md) — condition and branch types
- [README.md](README.md) — language overview and index
