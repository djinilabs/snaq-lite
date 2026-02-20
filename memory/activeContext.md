# Active context

## Just completed
- **Review and improve (symbols):** README updated for `run` → `Value`, `run_numeric`, `run_scalar`, symbols, and CLI `--numeric`. Symbolic substitution: division-by-zero during substitute now returns `RunError::DivisionByZero` (not `SymbolHasNoValue`). Doc: `SymbolRegistry` (symbols without value = not in map), `Value` (Display and `to_quantity`). Test: `run_numeric_symbolic_div_by_zero_returns_division_by_zero` for `(1+pi)/0`. All 118 tests and clippy pass.
- **Symbols:** Symbols (e.g. pi, π, e or any unknown identifier) are supported. Default evaluation returns `Value` (symbolic by default): `1 + π` → "1 + π", `3 + 2 + π + 1` → "6 + π". `SymbolRegistry` (built-ins pi/π, e), `SymbolicExpr`/`SymbolicQuantity` with simplification (Sum/Product), `Value::Numeric`|`Value::Symbolic`. IR: `LitSymbol`; resolve treats unknown idents as symbols; grammar has `"π"` → LitSymbol("pi"). `run()` returns `Result<Value, RunError>`; `run_numeric()` substitutes and returns `Quantity`; CLI `--numeric` for numeric output; WASM `evaluate_numeric()`.

## Just completed (earlier)
- **Unary minus:** Grammar and IR now support a leading minus (e.g. `-1`, `-(2*3)`). Added `ExprDef::Neg` and `ExprData::Neg`; Factor rule `"-" Factor => Neg`; resolve and value() handle Neg via `Quantity::neg`. Tests: `parse_unary_minus`, `eval_unary_minus`. All tests and clippy pass.

## Just completed (earlier)
- **Review and improve (SnaqNumber):** `SnaqNumber` now derives `Copy` (removes unnecessary clones in Quantity). Variance clamped to non-negative in Mul, Div, Mul<f64>, Div<f64> for float safety. Doc comments: propagation rules on `SnaqNumber`, `Quantity::value`/`variance` documented. Test `snaq_number_variance_always_non_negative` added. All 98 tests and clippy pass.
- **SnaqNumber migration:** Numeric values are now `SnaqNumber` (value + variance). Variance is propagated through Add/Sub/Mul/Div/Neg and scaling by f64; literal variance derived from f64 precision `(value * ε/2)²`. `Quantity` uses `number: SnaqNumber`; `Quantity::new(f64, unit)` / `from_scalar(f64)` build via `SnaqNumber::from_literal`; arithmetic uses `Quantity::with_number`. `SnaqNumber` re-exported from crate; `Quantity::value()` and `Quantity::variance()` accessors. All tests and clippy pass.

## Just completed (earlier)
- **Unit display fix:** Division units (e.g. `kilometers / hour`) now display as `kilometers/hour` instead of `kilometers/hour⁻¹`. In `Unit::fmt`, denominator factors use positive exponent for display (slash already means "per"). Test `unit_display_division_no_redundant_inverse` added. All tests and clippy pass.

## Just completed (earlier)
- **Phase 2 – Syntax and evaluation:** Grammar supports quantity literals (`Num`, `Num Ident`, `Ident`); parser produces `LitScalar`/`LitWithUnit`/`LitUnit`; two-step resolve converts to `Lit(Quantity)`. IR uses `ExprDef::Lit(Quantity)`; `value()` returns `Result<Quantity, RunError>`. `run()` returns `Result<Quantity, RunError>`; `run_scalar()` for dimensionless result. Errors: UnknownUnit, DimensionMismatch, DivisionByZero. CLI/WASM use `run()` and Display. All tests and clippy pass.
- **Phase 1 – Core model and SI:** Dimension, Unit, Quantity, prefix, unit/dimension registries; default_si_registry (m, s, kg, km, hour, minute).

## Just completed (Phase 3)
- **Phase 3 – Prefixes and simplification:** Prefix symbols in `prefix.rs`; `get_unit_with_prefix` in registry (longest-match prefix + base unit); Unit Display with prefix (e.g. km, µm) and ·/solidus/⁻¹; `Quantity::full_simplify` (dimensionless → scalar); `Quantity::full_simplify_with_registry` (prefer value in [0.1, 1000]).

## Just completed (Phase 4)
- **Phase 4 – Unit/dimension parity:** Extended default registry with Numbat-style units: Length (mile, au, parsec, light_year), Energy (joule, eV). Same names and conversion factors as Numbat for expressions like `1 mile`, `1 parsec`, `1 eV`, `100 km / hour`. More modules (time, imperial, cgs, etc.) can be added to the same built-in registry.

## Review and improve (done)
- **README:** Updated API to `run()` → `Quantity`, `run_scalar()`; added unit examples (100 km/hour, 1 mile, 1.5 km + 500 m).
- **Tests:** Added `run_division_by_zero_returns_err` (1/0, 3 m / 0 s) and `run_dimension_mismatch_returns_err` (1 m + 1 s).
- **API:** `run_with_registry(input, &UnitRegistry)` for custom registries; `run()` delegates to it. Exported `UnitRegistry`; added `Clone` to `UnitRegistry` and `DimensionRegistry`. Doc comments clarified (default units, when to use `run_scalar`).

## Just completed
- **SI units:** All BIPM SI base units (m, kg, s, A, K, mol, cd) and SI derived units with special names: J, C, V, F, ohm, S, Wb, T, H, Hz, N, Pa, W, lm, lx, Bq, Gy, Sv, kat; long forms (coulomb, volt, farad, ohm, siemens, weber, tesla, henry, lumen, lux, becquerel, gray, sievert, katal) and celsius. Removed these from unsupported list; tests and clippy pass.
- **Review and improve:** README updated with full SI unit list and examples (1 second, 1 volt). Unit registry refactored with `add_derived_alias` helper to reduce repetition; long-form base unit aliases added (ampere, amperes, kelvin, kelvins, mole, moles, candela, candelas, gram, grams). Test `long_form_base_unit_aliases` added. All tests and clippy pass.

## Just completed
- **Division alias "per":** Grammar accepts `per` as alias for `/` (e.g. `3 kilometers per hour`). LALRPOP string literal has higher lexer priority than Ident, so "per" is parsed as operator. Test `run_per_alias_for_division`; README and systemPatterns updated.
- **Review and improve (per):** Grammar comment on lexer priority for "per"; README example shows result (`3 km/hour`); `run()` doc mentions "per"; added `parse_per_same_as_div`, `parse_ident_containing_per_still_ident`, and `run_scalar("6 per 2")` in `eval_div`. All tests and clippy pass.

## Just completed
- **Implicit multiplication:** Grammar uses `ImplicitMulRight` (Num or `"(" Expr ")"`) so only number or parenthesized expr can be RHS of implicit mul (e.g. `10 20` → 200, `2 (3 + 4)` → 14, `10 m 2` → 20 m). `10 m` stays one quantity literal; no Term-Ident implicit mul. Tests: `parse_implicit_mul`, `eval_implicit_mul`, `eval_implicit_mul_with_units`. Test `parse_invalid_float_is_error` renamed to `parse_1_2_3_as_implicit_mul` (e.g. `1.2.3` now parses as 1.2 * .3 = 0.36). systemPatterns updated.

## Review and improve (implicit multiplication)
- **Docs:** systemPatterns.md now states implicit mul only when RHS is number or (expr); README Language + Examples mention implicit mul with `10 20`, `2 (3+4)`; `run()` doc in lib.rs updated.
- **Tests:** `parse_quantity_literal` asserts "10 m" is LitWithUnit (not Mul); `eval_implicit_mul` adds "10 20 + 5" == 205 (precedence); `parse_implicit_mul_rhs_not_ident` documents that "2 3 m" is parse error (RHS of implicit mul cannot be Ident). All tests and clippy pass.

## Just completed
- **Review and improve (division by zero / ±∞):** Added `Quantity::is_infinite()` and `Quantity::is_finite()`; `convert_to` short-circuits when value is infinite (same dimension, unit change only). `Quantity::div` uses `is_sign_positive()` for ±∞. `QuantityError::DivisionByZero` documented as 0/0 (indeterminate). Test `quantity_convert_to_preserves_infinity`; div tests assert `is_infinite()`/`is_finite()`. README: division-by-zero note and example (`1/0` → `inf`). All tests and clippy pass.
- **Division by zero and ±infinity (no NaN):** Nonzero/0 → ±∞ (sign of numerator); 0/0 → DivisionByZero. SnaqNumber::from_literal sets variance 0 for infinite x. Quantity::div branches: 0/0 Err, nonzero/0 Ok(±∞). Tests: run_division_by_zero_nonzero_yields_infinity, run_zero_over_zero_returns_err, run_arithmetic_with_infinity; quantity and SnaqNumber tests for inf and div-by-zero.

## Next steps
- Optional: add more unit modules (time: week, year; imperial: foot, pound; etc.) or .nbt loader for full Numbat module set.
- Optional: variance in symbolic form; user-defined symbols (let x = 2); more built-in constants (φ, c).
