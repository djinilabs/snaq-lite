# Vectors

This document describes vector literals, transpose, orientation, and how vectors interact with scalars and other vectors, including runtime lazy/streaming semantics relevant to users.

## Vector literal

- **Syntax:** `[ expr, expr, ... ]` or `[]`.
- Elements are expressions separated by commas. They can be any expression (scalars, quantities, symbols, or nested vectors).
- **Nested vectors** are allowed: e.g. `[[1, 2], [3, 4]]` is a vector whose elements are two vectors.
- Vector literal elements are evaluated **lazily** when consumed. This means partial consumers (for example index access) can return without evaluating later elements.

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
  - **`V.map(fn (x) => body)`** or **`V.map(fn x => (body))`** — returns a vector where each element is the result of applying the function to the corresponding element. The argument can be a **user function** (one parameter) or a **single-argument built-in** (e.g. `sqrt`, `sin`, `cos`, `tan`). Example: `[1, 2, 3].map(fn (x) => (x+1))` → `[2, 3, 4]`; `[1, 2, 3].map(sqrt)` → `[1, 1.414..., 1.732...]`. You can pass a variable that holds a built-in: `f = sqrt; [1, 4, 9].map(f)` → `[1, 2, 3]`. Mapping is lazy: element computation happens as the result is consumed.
  - **`V.take(start, length)`** — same as the built-in `take(V, start, length)`: returns a streaming slice from index `start` (0-based) with up to `length` elements. Example: `[1, 2, 3, 4].take(1, 2)` → `[2, 3]`.
  - **`V.sum()`** — sum of all elements (scalar). Empty vector → `0`. Same dimension required.
  - **`V.mean()`** — arithmetic mean (sum / length). Empty vector → error.
  - **`V.min()`**, **`V.max()`** — minimum or maximum element (scalar). Empty vector → error. Elements must be numeric, same dimension.
  - **`V.dot(other)`** — dot product with another vector (element-wise pairing; same length required). Returns a scalar.
  - **`V.norm()`** — L2 norm (Euclidean length): √(sum of squares of elements). Empty vector → `0`. Same dimension required. Computed as a streaming reduction.
  - **`V.product()`** — product of all elements (scalar). Empty vector → `1`. Same dimension required.
  - **`V.variance()`** — population variance (mean of squares minus square of mean). Empty vector → error. Result has squared dimension (e.g. m² for lengths in m).
  - **`V.stddev()`** — standard deviation (√ of variance). Empty vector → error.
  - **`V.median()`** — median of elements (middle value or average of two middles). Empty vector → error. Same dimension required. For non-replayable streams (for example direct input-handle streams), this returns an error because exact median requires replay/materialization.
  - **`V.quantile(p)`** — sample quantile; `p` in [0, 1] (e.g. 0.5 for median). Empty vector → error. Same dimension required. For non-replayable streams, this returns an error because exact quantile requires replay/materialization.
  - **`V.all()`** — true if every element is true; **`V.any()`** — true if any element is true. Elements must be boolean (e.g. from comparisons). Empty vector: `all()` → true, `any()` → false.

Numeric index access (e.g. `V.0`, `V.1`) is unchanged: use a **number** after the dot for single-element access; use an **identifier** (e.g. `length`, `map`) for property or method access. Unknown property or method names return **unknown property** or **unknown method**.

Reduction methods are evaluated by consuming vector streams; they do not require vectors to be pre-materialized in memory before computation starts. The exact-order statistics methods (`median`, `quantile`) are the intentional exception for non-replayable streams.

### Math and statistics (for students)

The methods **sum**, **mean**, **min**, **max**, **dot**, **norm**, **product**, **variance**, **stddev**, **median**, and **quantile** support typical science and math workflows: net force (sum of force vectors), average value (mean), bounds (min/max), dot product and vector length (norm), compound growth (product), and spread (variance, stddev). All reduction methods require elements to have the same dimension (or be boolean for **all**/**any**). Empty-vector behaviour: **sum** → 0, **product** → 1, **norm** → 0; **mean**, **min**, **max**, **variance**, **stddev** return an error.

## Display

Vectors are displayed in a list-like form, e.g. `[1, 2, 3]` or `[1 m, 2 m]`. Nested vectors may be shown with nested brackets. If the language supports sparse or undefined elements, they may be shown as `?`.

## Limits (current)

- **Converting a vector to a single quantity:** Not supported. If the result of an expression is a vector and you request a numeric quantity (e.g. `run_numeric`), the runtime returns an error: **operation not supported for vector**.
- **Binding a vector to a variable:** Supported. You can bind a vector to a name and use it in later expressions (see [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md)).
- **Transpose and outer product memory:** Transpose and column×row outer product are lazy at the API level, but mathematically require buffering parts of the input while producing output columns.
- **Buffer safety guards:** The runtime enforces bounded buffering for these operators:
  - `transpose` uses `SNAQ_TRANSPOSE_BUFFER_LIMIT` (default `100000` buffered elements per phase).
  - `outer product` uses `SNAQ_OUTER_LEFT_BUFFER_LIMIT` (default `100000` left-side buffered elements).
  - If a limit is exceeded, evaluation fails with an explicit runtime error instead of continuing with unbounded memory growth.

## See also

- [SYNTAX.md](SYNTAX.md) — vector literal and postfix `'`
- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — value types
- [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md) — vector comparisons
- [FUNCTIONS.md](FUNCTIONS.md) — functions applied to vectors (element-wise)
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — expected vector, length mismatch, unsupported vector operation
- [README.md](README.md) — language overview and index
