# Multiple expressions and blocks

The language supports multiple expressions at the top level and inside blocks. The result of a program or block is the value of the **last** expression.

## Top-level expressions

At the root level you can write several expressions:

- **One per line:** expressions are separated by newlines. Blank lines are allowed and do not add an expression.
- **Semicolon-separated:** you can put several expressions on one line using `;` as a separator.

The **program result** is the value of the **last** expression. Earlier expressions are evaluated in order but their values are only used for side effects (e.g. if you add user-defined state later); for now, only the last value is returned.

### Examples

| Input | Result |
|-------|--------|
| `1` | 1 |
| `1` (newline) `2` | 2 |
| `1; 2; 3` | 3 |
| `1 + 1` (newline) `2 + 2` | 4 |
| (blank line) `1` (blank) `2` | 2 |

## Blocks

A **block** is written with curly braces `{` and `}`. Inside a block the same rules apply: you can write multiple expressions, one per line or separated by `;`, and blank lines are allowed.

- The **value of a block** is the value of the **last** expression in the block.
- If a block has **no** expressions (empty block `{}`), its value is **undefined**.
- A block is an **expression**: you can use it anywhere an expression is allowed (e.g. `2 * { 3; 4 }` evaluates to 8).

### Examples

| Expression | Result |
|------------|--------|
| `{ 1; 2 }` | 2 |
| `{ 10` (newline) `20 }` | 20 |
| `{}` | undefined |
| `2 * { 3; 4 }` | 8 (block yields 4, then 2 * 4) |
| `{ 1; { 2; 3 } }` | 3 (nested block yields 3) |

## Undefined

When the result is **undefined** (e.g. empty program or empty block):

- `run()` returns `Ok(Value::Undefined)`.
- Display (e.g. CLI or `run_format`) shows `"undefined"`.
- Converting to a quantity (e.g. `run_numeric("")`, `run_numeric("{}")`, or `value.to_quantity()`) returns an error: result is undefined.

## Summary

- **Separators:** newline or `;` between expressions; blank lines allowed.
- **Program / block result:** last expression value, or the last binding’s value (RHS) if the last item is an assignment, or **undefined** if the block is empty.
- **Blocks:** `{ ... }`; same rules inside; block is an expression.
