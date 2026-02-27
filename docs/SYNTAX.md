# Syntax

This document describes the lexical structure and operator precedence of the language. It does not describe how the language is implemented.

## Tokens

### Numbers

- **Integer:** one or more digits (e.g. `0`, `42`).
- **Decimal:** digits, optional decimal point, digits (e.g. `3.14`, `.5`, `10.`).
- **Exponent:** optional `e` or `E` followed by optional `+` or `-` and digits (e.g. `1e-2`, `2.5E+3`).

Invalid numeric forms (e.g. `1.2.3` parsed as two tokens) can lead to parse errors or unexpected parses.

### Identifiers

- Start with a **letter** (a–z, A–Z) or **underscore** `_`.
- Then zero or more **letters**, **digits**, or **underscores**.

Examples: `x`, `speed`, `unit_name`, `_private`.

### Keywords and word boundaries

The following are reserved as keywords and are recognized only when they form a **whole word** (not when they are part of a longer identifier):

- `if`, `then`, `else` — conditionals
- `per` — alias for division (e.g. "meters per second")
- `as` — unit conversion (e.g. "10 km as m")

So `aspect` is a single identifier (the `as` in the middle is not treated as the keyword). The same rule applies to `per` and `if`/`then`/`else`.

### Unicode

- The character **π** (Unicode U+03C0) is recognized as the constant pi, equivalent to the identifier `pi` when used as a symbol.

### Operators and punctuation

| Token | Meaning |
|-------|--------|
| `+` `-` `*` `/` | Arithmetic |
| `per` | Division (same as `/`) |
| `as` | Unit conversion |
| `=` | Assignment (binding); single `=` only |
| `==` `!=` `<` `<=` `>` `>=` | Comparison |
| `~` | Explicit precision (value ~ error) |
| `'` | Postfix transpose (vectors) |
| `\|` | Absolute value: `\|expr\|` is equivalent to `abs(expr)` |
| `(` `)` | Grouping and function calls |
| `[` `]` | Vector literals |
| `{` `}` | Blocks |
| `,` | Separator in lists and function arguments |
| `:` | Named argument (e.g. `max(a: 1, b: 2)`) |
| `;` | Expression separator |

Comparison uses two-character tokens where applicable: `==`, `!=`, `<=`, `>=` are one token each; `<` and `>` alone are separate tokens.

## Whitespace

- **Space** and **tab** are ignored (skipped between tokens).
- **Newline** is significant: it separates expressions at the top level and inside blocks. Blank lines are allowed and do not add an extra expression.

There is **no comment syntax** in the language.

## Operator precedence

From **weakest** (lowest precedence) to **strongest** (highest precedence):

1. **Conditional** — `if condition then expr else expr`
2. **Comparison** — `==`, `!=`, `<`, `<=`, `>`, `>=` (all same level)
3. **Addition, subtraction, unit conversion** — `+`, `-`, `as` (left-associative)
4. **Multiplication, division, implicit multiplication** — `*`, `/`, `per`, and implicit mul (left-associative)
5. **Explicit precision** — `~` (e.g. `10 ~ 2`)
6. **Postfix transpose** — `'` (e.g. `[1,2,3]'`)
7. **Unary minus** — `-` applied to a factor (e.g. `-x`, `-(1+2)`)

Example: `5 + 10 ~ 2` is parsed as `5 + (10 ~ 2)`, and `a * b as m` is parsed as `(a * b) as m`.

## Implicit multiplication

You can omit `*` in two cases only:

- **Number and then identifier(s):** e.g. `10 20` → 200, `2 pi rad` → 2 × π × rad, `1 s` → 1 second.
- **Expression and then number or parenthesized expression:** e.g. `2 (3+4)` → 14.

Implicit multiplication is **not** allowed when the right-hand side would be a bare identifier that starts a unit or symbol. For example, `2 3 m` is a **parse error**: the grammar does not allow implicit multiplication between two identifiers (here `3` and `m`). Write `2 * 3 * m` or `6 m` instead.

## Binding vs comparison

- **Single `=`** — Assignment (variable binding). Used in `name = expression`.
- **Double `==`** — Equality comparison. Used in `a == b`.

Chained assignment is **right-associative**: `A = B = 42` means `A = (B = 42)`; both `A` and `B` are bound to 42, and the value of the expression is 42.

## Absolute value

- **Notation:** `| expr |` — vertical bars around an expression denote absolute value.
- **Semantics:** Equivalent to calling the built-in `abs(expr)`. Nested bars are allowed: e.g. `|2 + |-3||` evaluates to 5.

## Chained comparisons

- **Form:** `a < b < c` or `a <= b <= c` (and similarly with `>` and `>=`). The grammar supports **exactly three** operands in one chain (e.g. `1 < 2 < 3`).
- **Semantics:** Same as the conjunction of two pairwise comparisons. For example, `1 < 2 < 3` means `(1 < 2) and (2 < 3)`; the result is a single boolean (FuzzyBool). All operators in the chain must be in the same “direction”: all ascending (`<`, `<=`) or all descending (`>`, `>=`). Mixed chains like `1 < 2 <= 3` are allowed (both ascending).
- **Longer chains:** Four or more operands (e.g. `a < b < c < d`) are parsed as a chained comparison of the first three, then compared with the fourth: `(a < b < c) < d` (the left side is a boolean, which is not numeric; see [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md)). For multiple comparisons in one expression, use separate comparisons combined with `if`/`then`/`else` or write them as separate expressions.

## Unit conversion (grammar)

The right-hand side of `as` must be a **unit-only expression**: identifiers combined with `*`, `/`, or `per` (e.g. `m`, `meters per second`, `newton per squareinch`). Numbers and symbols are not allowed there. See [UNITS_AND_QUANTITIES.md](UNITS_AND_QUANTITIES.md) for semantics.

## Known parser limitation

Full expressions are accepted in if/then/else, vector elements, parentheses, and top-level/comparison (ExprReset workaround for LALRPOP #596). Chained comparisons and absolute value work in all these contexts. In other nested positions you might still get a parse error such as “expected one of …, before end of input” (or “before: Then”, “before: Comma”) even for valid-looking expressions like `1 == 2` or `[1.0 < 2.0, 1.0 == 2.0]`. This is a known limitation of the parser (LALRPOP #596). Chained comparisons (e.g. `1 < 2 < 3`) and absolute value `|x|` work in contexts where they parse; fixing the remaining contexts may require a parser change.

## See also

- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — numeric and vector literal semantics
- [BLOCKS_AND_EXPRESSIONS.md](BLOCKS_AND_EXPRESSIONS.md) — how expressions and blocks form a program
- [VARIABLE_BINDINGS.md](VARIABLE_BINDINGS.md) — binding syntax and scope
- [README.md](README.md) — language overview and index
