# Conditionals: if / then / else

The language supports expression-oriented conditionals with the syntax:

```text
if condition then expression else expression
```

The whole construct is an expression and returns a value. The condition and both branches can be any expression.

## Condition type

The **condition** must evaluate to a boolean-like value:

- **true** or **false** (crisp): only the matching branch is evaluated and returned.
- **uncertain(probability)**: both branches are evaluated and combined (superposition).

If the condition evaluates to a number or a symbolic expression (e.g. `if 1 then 10 else 20`), the runtime returns an error: the condition must be a comparison or something that yields a boolean.

## Crisp behaviour

When the condition is clearly true or false (e.g. `1 < 2`, or a constant-folded comparison), only one branch is used:

- `if 1 < 2 then 10 else 20` → **10**
- `if 1 > 2 then 10 else 20` → **20**

This avoids evaluating the other branch.

## Fuzzy superposition

When the condition is **uncertain(probability)** (e.g. a statistical comparison where both sides have variance and the result is in the uncertain band), the runtime evaluates **both** branches and blends the results:

- **Numeric:** Both branches are numbers (with optional units). The two quantities are converted to a common unit (same dimension required); the result is a new number in that unit whose mean is the weighted average and whose variance is given by the Law of Total Variance (mixture of the two outcomes).
- **Symbolic:** One or both branches are symbolic. The result is the symbolic expression `P · then_branch + (1 − P) · else_branch` (after scaling to a common unit if needed). Again, both branches must have the same dimension.

Example (equal means ⇒ probability 0.5):

- `if 1 > 1 then 10 else 20` → numeric **15** (0.5·10 + 0.5·20).

## Type rules

- Both branches must be **blendable**: numeric or symbolic. You cannot mix a number with a vector or a boolean in the branches; that yields a type error.
- The condition must evaluate to a boolean (true, false, or uncertain), not to a number or a symbolic expression.

## Examples

| Expression | Result |
|------------|--------|
| `if 1 < 2 then 10 else 20` | 10 (crisp then) |
| `if 1 > 2 then 10 else 20` | 20 (crisp else) |
| `if 1 > 1 then 10 else 20` | 15 (superposition, P=0.5) |
| `if 1 > 1 then pi else 2 * pi` | symbolic weighted sum in π |
| `if 1 then 10 else 20` | error: condition must be boolean |
| `if 1 > 1 then 10 else [1, 2]` | error: branches must both be numeric or symbolic |

## See also

- [README.md](README.md) — language overview and index
- [SYNTAX.md](SYNTAX.md) — if/then/else syntax and precedence
- [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md) — condition type (true, false, uncertain)
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — expected condition, if branch type mismatch
