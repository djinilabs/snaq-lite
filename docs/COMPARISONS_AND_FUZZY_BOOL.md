# Comparisons and FuzzyBool

This document describes the comparison operators and the boolean-like result type (FuzzyBool). It does not describe the statistical or implementation details of uncertainty.

## Comparison operators

The language provides six comparison operators. **Same dimension** is required for both operands (e.g. length with length, time with time). Mixing dimensions (e.g. `1 m` and `1 s`) yields a **dimension mismatch** error.

| Operator | Meaning |
|----------|--------|
| `==` | Equal |
| `!=` | Not equal |
| `<` | Less than |
| `<=` | Less than or equal |
| `>` | Greater than |
| `>=` | Greater than or equal |

Precedence: comparisons bind **weaker** than addition and subtraction (see [SYNTAX.md](SYNTAX.md)). So `a + b < c + d` is parsed as `(a + b) < (c + d)`.

## Chained comparisons

You can write **chained comparisons** with exactly three operands and the same direction: e.g. `1 < 2 < 3` or `3 > 2 > 1`. Semantics: `a < b < c` means `(a < b) and (b < c)`; the result is a single FuzzyBool. All operators in the chain must be ascending (`<`, `<=`) or all descending (`>`, `>=`). Mixed ascending chains like `1 < 2 <= 3` are allowed. See [SYNTAX.md](SYNTAX.md) for the exact grammar (three operands only; longer chains are not supported as a single expression).

## Result type: FuzzyBool

The result of a comparison is a **FuzzyBool**: one of

- **`true`** — the comparison is considered true (with high confidence).
- **`false`** — the comparison is considered false (with high confidence).
- **`uncertain(probability)`** — the operands have uncertainty (variance), and the comparison falls in an uncertain band; the probability indicates how likely the comparison is to hold.

When operands are **exact** (no variance or zero variance), the result is **crisp** `true` or `false`. When operands have **variance** (e.g. from literal precision or from `value ~ error`), the runtime may return `uncertain(p)` if the two distributions overlap enough that the comparison cannot be decided with sufficient confidence. The threshold used is fixed (e.g. 95% confidence); exact formulas are not part of this user-facing doc.

**Display:** Results are shown as the string `"true"`, `"false"`, or `"uncertain(prob)"` where `prob` is a number.

## Scalar comparison

- **Both operands scalar (same dimension):** One comparison is performed; result is a single FuzzyBool (true, false, or uncertain).
- **Equality with zero variance:** When both sides have zero variance and equal means, `==` is true and `!=` is false; when means differ, `==` is false and `!=` is true.

## Vector comparison

When one or both operands are **vectors**, the comparison is applied according to **orientation** (column vs row). See [VECTORS.md](VECTORS.md) for orientation.

- **Column with column** or **row with row** (same orientation, same length): **Element-wise** comparison. Each pair of elements is compared; the result is a vector of FuzzyBools (same orientation and length). If lengths differ, the runtime returns a **vector length mismatch** error.
- **Column with row:** **Outer** comparison. Each element of the column is compared with each element of the row; the result is a vector of column vectors (a matrix of FuzzyBools).
- **Row with column:** The comparison is **reduced** to a scalar: the two vectors are combined (e.g. sum or product depending on the operation), then the two scalar results are compared. For `==`, `!=`, `<`, `<=`, `>`, `>=`, the semantics are defined so that one scalar comparison is produced (e.g. sum(left) vs sum(right)).

Same **dimension** is required for the scalar operands in each comparison; length mismatch is required for element-wise and outer cases as above.

## Use cases

- **Conditions:** FuzzyBool is the expected type for the condition in `if condition then ... else ...`. Crisp true/false choose one branch; uncertain leads to superposition (see [CONDITIONALS.md](CONDITIONALS.md)).
- **Display:** Comparisons can be printed as `true`, `false`, or `uncertain(…)`. Converting a comparison result to a single numeric quantity (e.g. via `run_numeric`) is **not** supported and returns an error (boolean result).

## See also

- [SYNTAX.md](SYNTAX.md) — operator precedence
- [CONDITIONALS.md](CONDITIONALS.md) — if/then/else and FuzzyBool conditions
- [VECTORS.md](VECTORS.md) — vector orientation and vector–vector operations
- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — value types
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — dimension mismatch, length mismatch, boolean result
- [README.md](README.md) — language overview and index
