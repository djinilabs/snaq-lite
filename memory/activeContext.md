# Active context

## Just completed
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

## Next steps
- Optional: add more unit modules (time: week, year; imperial: foot, pound; etc.) or .nbt loader for full Numbat module set.
