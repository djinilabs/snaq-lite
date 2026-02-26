# Dates and temporal literals

This document describes calendar dates in snaq-lite: syntax, grain semantics, arithmetic (Date ± Time, Date − Date), and comparison (interval overlap → true / false / uncertain).

## Syntax: the `@` sigil

Temporal literals are written with an **`@`** prefix followed by an ISO 8601–style date or date-time. The form determines the **grain** (precision) of the value.

| Form | Example | Grain |
|------|---------|--------|
| `@YYYY` | `@2026` | Year |
| `@YYYY-MM` | `@2026-02` | Month |
| `@YYYY-MM-DD` | `@2026-02-26` | Day |
| `@YYYY-MM-DDTHH` | `@2026-02-26T14` | Hour |
| `@YYYY-MM-DDTHH:MM` | `@2026-02-26T14:30` | Minute |
| `@YYYY-MM-DDTHH:MM:SS` | `@2026-02-26T14:30:00` | Second |

- All times are interpreted in **UTC**.
- The letter **`T`** separates date and time (no space).
- Invalid or incomplete sequences (e.g. `@20`, `@2026-13-01`, `@2026-02-26T14:30:S`) produce a parse or runtime error (**invalid temporal literal**).

## Grain semantics

A date value represents a **bounded interval** in time:

- **Anchor:** the start of the interval (e.g. start of the year, month, day, or time component).
- **Grain:** how fine the interval is (Year → Month → Day → Hour → Minute → Second).

For example, `@2026` is the whole year 2026; `@2026-02` is the whole month February 2026; `@2026-02-26` is that full day in UTC.

## Arithmetic

### Date + Time and Date − Time

- **Date + duration:** You can add a **time quantity** (e.g. `3 * hour`, `5 days`) to a date. The result is a new date with the **same grain** as the original; the anchor is shifted by the duration.
- **Date − duration:** Subtracting a time quantity shifts the anchor backward (same grain).
- **Grain rule:** The duration’s unit must not be **finer** than the date’s grain. For example:
  - `@2026` (year grain) + `3 hours` → **error** (incompatible date grain: year is coarser than hour).
  - `@2026-02-26` (day grain) + `3 hours` → allowed (day is at least as fine as hour).
  - `@2026-02-26T14` (hour grain) + `30 minutes` → allowed.

If you add or subtract a duration that is finer than the date’s grain, the runtime returns an **incompatible date grain** error.

### Date − Date

- **Date − Date** yields a **duration** (time quantity) in **seconds**: the difference between the two dates’ anchors. For example, `@2026-02-26 - @2026-01-01` gives the number of seconds between the start of those days.

## Comparison (date vs date)

Comparing two dates uses **interval bounds**:

- Each date is an interval `[min, max]` (from start to end of the grain window).
- **Strictly before:** If the end of A is before the start of B, then A < B, A ≤ B → **true**; A > B, A ≥ B, A == B → **false**; A != B → **true**.
- **Strictly after:** If the start of A is after the end of B, then A > B, A ≥ B → **true**; A < B, A ≤ B, A == B → **false**; A != B → **true**.
- **Overlap:** If the two intervals overlap (e.g. `@2026` and `@2026-02`), the result is **uncertain**: all of `<`, `<=`, `>`, `>=`, `==`, `!=` yield **uncertain(0.5)** (or equivalent), because the comparison cannot be decided from the intervals alone.

So:

- Disjoint intervals → **true** or **false** as above.
- Overlapping intervals → **uncertain**.

Comparison is only defined **between two dates**. Comparing a date with a number or other type is an error (e.g. “comparison with date requires both operands to be dates”).

## Use cases

- **Anchors and windows:** Use `@YYYY-MM-DD` for a specific day, or `@YYYY-MM` for a month, then add durations (e.g. `@2026-01-01 + 7 days`) to move within or past the window.
- **Spans:** Use `date1 - date2` to get the span in seconds (or convert to another time unit if needed).
- **Filtering / conditions:** Compare two date literals or variables; non-overlapping intervals give crisp true/false; overlapping intervals give uncertain, which can be used in `if condition then ... else ...` (see [CONDITIONALS.md](CONDITIONALS.md)).

## Display

Date values are shown in a canonical form that matches the grain, e.g. `@2026`, `@2026-02-26`, or `@2026-02-26T14:30:00`.

## Limits and edge cases

- **`run_numeric`:** A program that evaluates to a date (e.g. `@2026` or `d = @2026-02-26; d`) cannot be converted to a single quantity. `run_numeric` will return an error (invalid argument: date value cannot be converted to quantity). Use `run()` or `run_with_registry()` to get a `Value`, which may be a date.
- **Vectors of dates:** A vector whose elements are dates (e.g. `[ @2026, @2027 ]`) is not explicitly supported for date-specific operations; use scalar date arithmetic and comparisons as needed.

## See also

- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — value types (Date is one of them)
- [COMPARISONS_AND_FUZZY_BOOL.md](COMPARISONS_AND_FUZZY_BOOL.md) — FuzzyBool and comparison semantics
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — invalid temporal literal, incompatible date grain
