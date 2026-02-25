# Vectors

This document describes vector literals, transpose, orientation, and how vectors interact with scalars and other vectors. It does not describe internal streaming or lazy representation.

## Vector literal

- **Syntax:** `[ expr, expr, ... ]` or `[]`.
- Elements are expressions separated by commas. They can be any expression (scalars, quantities, symbols, or nested vectors).
- **Nested vectors** are allowed: e.g. `[[1, 2], [3, 4]]` is a vector whose elements are two vectors.

By default, a vector literal has **column** orientation: it is treated as a single column of elements.

## Transpose (postfix `'`)

- **Syntax:** `expression'` — the expression must evaluate to a vector.
- **Effect:** **Transpose** flips the **orientation** of the vector:
  - Column → row
  - Row → column
- Applying transpose twice returns to the original orientation (e.g. column → row → column).

Examples: `[1, 2, 3]'` is the same three elements as a **row**. `[1, 2, 3]''` is back to a column.

If the operand is **not** a vector (e.g. a scalar or a symbolic expression), the runtime returns an error: **transpose requires a vector**.

## Orientation (column vs row)

Every vector has an **orientation**:

- **Column** — default for vector literals and for certain operation results (e.g. outer product yields columns).
- **Row** — e.g. after a single transpose of a column.

Orientation affects how **vector–vector** operations are interpreted (see below). It does not change how vectors are **displayed**: they are shown as `[ ... ]` (or the documented display format). Undefined or missing elements may be shown as `?` when displayed.

## Vector and scalar

When one operand is a **vector** and the other a **scalar** (or quantity):

- **Arithmetic:** `+`, `-`, `*`, `/` — applied **element-wise** to each element of the vector. Example: `[1, 2, 3] + 10` → `[11, 12, 13]`. Same for subtraction, multiplication, division (scalar on left or right as defined).
- **Functions:** Unary functions such as `sin`, `cos`, `tan` accept a vector argument and apply **element-wise**. Example: `sin([0 rad, pi rad])` → vector of results.
- **Unary minus:** `-vector` is element-wise negation.

The result is always a **vector** with the same orientation and length as the vector operand.

## Vector and vector

When **both** operands are vectors, the operation depends on **orientation**:

- **Column with column** or **row with row** (same orientation): **Element-wise** (zip). Each pair of elements is combined; the result is a vector of the same orientation and length. **Same length** is required; otherwise the runtime returns **vector length mismatch**.
- **Column with row:** **Outer product**. Each element of the column is combined with each element of the row; the result is a **vector of column vectors** (a matrix). So the result has one column per element of the **row** (second operand), and each column has one element per element of the **column** (first operand).
- **Row with column:** **Reduced** to a scalar:
  - For **multiplication:** dot product (sum of products of corresponding elements) → one scalar.
  - For **addition** or **subtraction:** sum of left elements op sum of right elements → one scalar.
  - For **division:** not defined; the runtime returns an error or unsupported behaviour.
  - For **comparisons:** the two scalars (e.g. sums) are compared → one FuzzyBool (see [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md)).

Same **dimension** (or type) is required where applicable (e.g. element-wise arithmetic and comparisons).

## Slicing and indexing

### take(vector, start, length)

- **Syntax:** `take(vector, start, length)` — a built-in with three arguments.
- **Arguments:** `vector` must evaluate to a vector; `start` and `length` must be numeric (non-negative; truncated to integers).
- **Effect:** Returns a **streaming vector** (slice) containing elements from index `start` (0-based) for up to `length` elements. Out-of-range (e.g. start beyond the end, or length larger than remaining elements) yields fewer elements or an empty vector; no error.
- **Example:** `take([1, 2, 3, 4], 1, 2)` → `[2, 3]`.

### Single-element access: V[index] and V.0, V.1, …

- **Syntax:** `expression[index]` or `expression . number` (e.g. `V.0`, `V.1`). The bracket form accepts any expression for the index; the dot form is a literal non-negative integer index.
- **Effect:** The base expression must evaluate to a **vector**. The index is 0-based. The result is the **single element** at that index (a scalar value, not a one-element vector). If the index is out of bounds, the runtime returns **index out of bounds**. The index must be a non-negative integer (numeric); otherwise the runtime returns **invalid index**.
- **Examples:** `[1, 2, 3, 4][2]` → `3`; `[1, 2, 3, 4].0` → `1`; `[1, 2, 3, 4].1` → `2`.

### Properties and methods (dot notation)

Vectors support **properties** (no arguments) and **methods** (with arguments) using the `.` notation. The base expression must evaluate to a vector; otherwise the runtime returns **transpose requires a vector** (or equivalent).

- **Properties**
  - **`V.length`** — number of elements (0-based count). Example: `[1, 2, 3].length` → `3`; `[].length` → `0`.

- **Methods**
  - **`V.map(fn (x) => body)`** — returns a vector where each element is the result of applying the function to the corresponding element. The function must take one parameter. Example: `[1, 2, 3].map(fn (x) => (x+1))` → `[2, 3, 4]`. Evaluation is **eager**: all elements are computed when `.map` is called. The function body can use variables from the surrounding scope (closure).
  - **`V.take(start, length)`** — same as the built-in `take(V, start, length)`: returns a streaming slice from index `start` (0-based) with up to `length` elements. Example: `[1, 2, 3, 4].take(1, 2)` → `[2, 3]`.

Numeric index access (e.g. `V.0`, `V.1`) is unchanged: use a **number** after the dot for single-element access; use an **identifier** (e.g. `length`, `map`) for property or method access. Unknown property or method names return **unknown property** or **unknown method**.

## Display

Vectors are displayed in a list-like form, e.g. `[1, 2, 3]` or `[1 m, 2 m]`. Nested vectors may be shown with nested brackets. If the language supports sparse or undefined elements, they may be shown as `?`.

## Limits (current)

- **Converting a vector to a single quantity:** Not supported. If the result of an expression is a vector and you request a numeric quantity (e.g. `run_numeric`), the runtime returns an error: **operation not supported for vector**.
- **Binding a vector to a variable:** Not supported in the current version. Binding a vector value to a name returns an error: **binding value not supported** (see [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) and [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md)).

## See also

- [SYNTAX.md](SYNTAX.md) — vector literal and postfix `'`
- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — value types
- [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md) — vector comparisons
- [FUNCTIONS.md](FUNCTIONS.md) — functions applied to vectors (element-wise)
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — expected vector, length mismatch, unsupported vector operation
- [README.md](README.md) — language overview and index
