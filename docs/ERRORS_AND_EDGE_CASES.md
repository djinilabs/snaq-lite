# Errors and edge cases

This document lists the main error conditions and edge cases you may encounter when writing expressions. It does not reference internal error types or code.

## Parse errors

- **Invalid literal:** A numeric token that cannot be parsed as a float (e.g. malformed exponent or invalid character sequence) produces a parse error.
- **Invalid syntax:** Expressions that do not match the grammar produce a parse error. Examples: `2 3 m` (implicit multiplication not allowed between these tokens), unmatched brackets, or invalid use of keywords.

## Runtime errors (when they occur)

| Situation | What you see (summary) |
|-----------|------------------------|
| **Unknown unit** | An identifier was used as a unit but is not in the unit registry. |
| **Dimension mismatch** | Two values that must have the same dimension do not (e.g. `1 m + 1 s`, or converting to an incompatible unit with `as`). If one side is dimensionless, it is shown as **none** (e.g. `dimension mismatch: none vs pascal`). |
| **Result is undefined** (from 0/0) | The expression `0/0` yields **undefined**. If you request a numeric result (`run_numeric("0/0")`), you get **result is undefined**. See below for division semantics. |
| **Symbol has no value** | You requested a numeric result (`run_numeric`) but a symbol (or unbound identifier) has no value in the symbol registry and is not bound in the program. |
| **Unknown function** | The call uses a name that is not a built-in and not bound to a user-defined function in scope. For user-defined functions: missing required argument (no default), unknown parameter name in a named argument, duplicate parameter name in a call, or too many arguments also yield an error. Calling a non-function value (e.g. applying arguments to a number) yields "expression is not callable". |
| **Cannot shadow built-in function** | You tried to bind a variable or user-defined function to a built-in name (`sin`, `cos`, `tan`, `max`, `min`). Those names cannot be redefined. |
| **Expected angle** | A trig function (sin, cos, tan) received an argument that is not an angle (e.g. length or dimensionless number without unit). The message may suggest adding `rad` (e.g. `sin(pi * rad)`). |
| **Operation not supported for vector** | An operation that expects a scalar was given a vector (e.g. converting the result to a single quantity when the result is a vector). |
| **Transpose requires a vector** | The postfix `'` was applied to a non-vector (e.g. a scalar or symbolic expression). |
| **Invalid index** | A vector index (e.g. `V[i]` or `take(V, start, length)`) used a non-numeric, negative, or non-finite value for the index, start, or length. |
| **Index out of bounds** | Single-element access `V[index]` or `V.0` was used with an index not less than the vector length. |
| **Unknown property** | Property access (e.g. `V.length`) used a name that is not supported on the value. Vectors support only `length`. |
| **Unknown method** | Method call (e.g. `V.map(...)`, `V.sum()`) used a name that is not supported on the value. Vectors support `map`, `take`, `sum`, `mean`, `min`, `max`, `dot`, `norm`, `product`, `variance`, `stddev`, `all`, `any`. Wrong number of arguments or wrong argument type (e.g. `map(1)` instead of a function, `map(max)` because max takes two parameters, or `dot` with non-vector) also yields an error. |
| **Empty vector reduction** | The methods **mean**, **min**, **max**, **variance**, and **stddev** require at least one element. Called on an empty vector, they return **empty vector: &lt;method&gt; requires at least one element**. |
| **Property/method on non-vector** | Dot access for a property or method (e.g. `(1).length`, `x.map(fn (a)=>a)`) was applied to a non-vector (scalar or symbolic). The runtime returns an error that a vector was expected. |
| **Vector length mismatch** | A vector operation (element-wise or similar) required two vectors of the same length; the lengths differed. |
| **Boolean result** | You requested a numeric quantity but the result is a comparison (true/false/uncertain). |
| **Expected condition** | The condition of `if ... then ... else ...` must evaluate to a boolean (true, false, or uncertain), not a number or symbolic expression. |
| **If branches type mismatch** | Both branches of `if ... then ... else ...` must be blendable (both numeric or both symbolic). You cannot mix e.g. number with vector or boolean. |
| **Both sides of ~ must be numeric** | The explicit-precision operator `~` was used with a symbolic, boolean, or vector operand. |
| **Precision must be strictly positive** | The right-hand side of `~` was ≤ 0 or non-finite. |
| **Result is undefined** | You requested a numeric quantity (or scalar) but the result is undefined (e.g. empty program or empty block). |
| **Binding value not supported** | You tried to bind a symbolic value to a variable (vectors are supported; only symbolic is not). Converting a function to a quantity (e.g. in unit conversion) also yields this (or a similar) error. |
| **Invalid argument** | A built-in function received an invalid argument (e.g. `sqrt(-1)` → argument must be non-negative). |

### How runtime and parse errors are shown

When the CLI (or any formatter that has the original source) reports an error, it may show:

- **Line and column** — e.g. `at line 1, column 7: division by zero`
- **A snippet** — the line of source with a squiggle (`~`) under the offending part

So for a runtime error that has a source location you might see something like:

```
at line 1, column 8: dimension mismatch: m vs s

   |
 1 | 1 m + 1 s
   | ~~~~~~~
```

Parse errors use the same style. If the source is not available, only the message is shown (e.g. `division by zero`).

Runtime errors from the main evaluation path (`run` / `run_with_registry`) carry a source span when available, so the CLI can show line/column and snippet for **all** error kinds (e.g. unknown unit, dimension mismatch, expected condition), not only division by zero.

## Division by zero

- **Nonzero / 0:** The result is **plus or minus infinity** (sign of the numerator). Infinity propagates through arithmetic and unit conversion (same dimension; only the unit may change).
- **0 / 0:** The result is **undefined** (not an error). `run("0/0")` yields the value **undefined** (displayed as such). If you request a numeric quantity (`run_numeric("0/0")`), you get the error **result is undefined** because undefined cannot be converted to a number.

There is **no NaN** in the language; only +∞ and −∞ for infinite values.

## Undefined result

- **When:** The program or block has **no** expressions, or the only expressions are bindings and the result is taken from an empty list (e.g. empty block `{}`, or empty input).
- **Value:** The result is **undefined**. Display shows something like `"undefined"`.
- **Conversion:** If you request a numeric quantity (e.g. `run_numeric("")` or `run_numeric("{}")`), the runtime returns an error: **result is undefined**.

## Binding limits

- **Allowed:** Binding a **numeric** value, a **FuzzyBool** (true/false/uncertain), a **user-defined function**, a **vector**, or **undefined** to a variable.
- **Not allowed (current):** Binding a **symbolic** value. The runtime returns an error: **binding value not supported** (or similar message).
- **Built-in names:** You cannot bind to `sin`, `cos`, `tan`, `max`, `min`, `sqrt`, or `take`; the runtime returns **cannot shadow built-in function**.

See [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) and [FUNCTIONS.md](FUNCTIONS.md) for scope and user-defined functions.

## See also

- [FUNCTIONS.md](FUNCTIONS.md) — user-defined functions and built-ins; cannot shadow built-in names
- [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) — binding limits
- [BLOCKS_AND_EXPRESSIONS.md](BLOCKS_AND_EXPRESSIONS.md) — undefined and empty blocks
- [PRECISION.md](PRECISION.md) — requirements for `~`
- [CONDITIONALS.md](CONDITIONALS.md) — condition and branch types
- [README.md](README.md) — language overview and index
