# Maps (objects)

Maps are key–value collections with **ordered** keys. Keys are strings; values can be any value (number, vector, nested map, undefined, etc.).

## Literal syntax

Map literals use JSON-like syntax with **unquoted** keys:

```text
{ key: value, other: 42, nested: { a: 1 } }
```

- At least one entry is required. Empty `{ }` is a **block**, not a map.
- Keys are identifiers (no quotes). The grammar distinguishes map from block by lookahead: `{ Ident :` starts a map; `{ Ident =` or `{ }` is a block.

## Access

- **Dot access:** `map.key` — looks up the property by name. Only works for keys that are valid identifiers (no spaces).
- **Bracket access:** `map[key]` — the content between `[` and `]` **is** the key. It can contain spaces; the key is **trimmed** (leading and trailing whitespace) before lookup. No quotes needed inside brackets.

Examples:

- `m.x` — key `"x"`
- `m[ x ]` — key `"x"` (trimmed)
- `m[ foo bar ]` — key `"foo bar"`

## Missing keys

If a key is not present, access returns **undefined** (no error).

## Binding

Maps can be bound to variables like other values:

```text
m = { a: 1, b: 2 }; m.a + m[b]
```

## Display and numeric conversion

- `run_format()` displays a map as `<map>`.
- `run_numeric()` / `to_quantity()` on a map returns an error (same as for vectors).

## Limits and errors

- **Numeric conversion:** Requesting a numeric result (e.g. `run_numeric("m = { a: 1 }; m")`) when the result is a map yields an error (operation not supported).
- **Index or member on scalar:** Using `(5)[0]` or `(5).x` on a number (or other non-vector, non-map value) returns an error that a vector was expected.
