# Variable bindings

Variables are **immutable** and **lexically scoped**. You bind a name to a value with `name = expression`. Later expressions in the same block (or the rest of the program) can use that name; the name refers to the value you bound.

## Syntax

- **Binding:** `Ident = Expr` in a block or at top level. Single `=` (assignment), not `==` (comparison). **Chained assignment** is allowed and is right-associative: `A = B = 42` binds both `A` and `B` to `42` and has value `42`.
- **Use:** Identifiers are resolved **scope-first**: if the name is bound in the current scope, it evaluates to that value. If not in scope, the identifier is then treated as a unit (e.g. `m`, `rad`) if it matches the unit registry, or as a symbol otherwise. So variables **shadow** unit names (e.g. `DEF=3; DEF+2` → `5` even though `DEF` could be parsed as the unit decafarad).

## Where bindings are allowed

- **Top level:** A program can be a list of bindings and expressions (newline- or `;`-separated). Example: `x = 10` then `x + 1` on the next line.
- **Blocks:** Inside `{ ... }` you can mix bindings and expressions. Example: `{ a = 2; b = 3; a * b }` → `6`.

## Semantics

- **Order:** Bindings and expressions are evaluated in order. An **assignment is an expression** whose value is the right-hand side. A binding evaluates its RHS in the current scope, extends the scope for the rest of the block (or program), and the binding expression’s value is that RHS. The **result** of a block (or program) is the value of the **last item** (last expression or last binding’s RHS).
- **Shadowing:** An inner block (or a later binding in the same block) can reuse a name. The innermost binding wins. Example: `x = 1` then `{ x = 2; x }` → `2`; the inner `x` shadows the outer one.
- **Immutability:** Once bound, a variable does not change. Reusing the same name in a later binding creates a **new** scope (shadowing), not an update.

## Examples

- `x = 10` then `x + 1` → `11`.
- `{ a = 2; b = 3; a * b }` → `6`.
- `x = 1` then `{ x = 2; x }` → `2` (inner `x` shadows).
- `x = 1` then `y = 2` (only bindings) → result is **2** (value of last binding, the RHS).
- `x = y = 42` (chained) → both `x` and `y` are bound to `42`; result is **42**. `x = y = 42` then `x + y` → **84**.

## Limits (current)

- Variables can hold **numeric** values, **fuzzy booleans**, **user-defined functions**, or **undefined**. Binding a **symbolic** or **vector** value to a variable is not supported yet; the runtime returns an error in those cases.
- **Built-in function names cannot be shadowed.** You cannot bind a variable (or a user-defined function) to the names `sin`, `cos`, `tan`, `max`, or `min`. An attempt to do so (e.g. `sin = 3` or `max = fn (a, b) => (a + b)`) returns a **cannot shadow built-in function** error. See [FUNCTIONS.md](FUNCTIONS.md) for user-defined functions and built-ins.
- **run_numeric** substitutes identifiers from the symbol and unit registries, but **names that are bound in the same program** are left as identifiers so that evaluation resolves them from scope. So variable bindings that shadow unit names (e.g. `DEF=3; DEF+2`) work in both **run()** and **run_numeric()** — the variable takes precedence over the unit.

## See also

- [FUNCTIONS.md](FUNCTIONS.md) — user-defined functions and built-ins; built-in names cannot be shadowed
- [README.md](README.md) — language overview and index
- [SYNTAX.md](SYNTAX.md) — binding syntax and chained assignment
- [BLOCKS_AND_EXPRESSIONS.md](BLOCKS_AND_EXPRESSIONS.md) — where bindings appear in programs and blocks
- [SYMBOLS.md](SYMBOLS.md) — resolution order (scope, unit, symbol)
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — binding value not supported
