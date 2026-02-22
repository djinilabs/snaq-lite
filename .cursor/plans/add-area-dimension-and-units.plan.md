# Add Area dimension and area units

## Overview

Add an Area dimension (Length²), area units (m², are, hectare, km², squareinch, etc.), shorthand symbols, no-underscore names, and treat **hectare as hecto × are** (1 are = 100 m², 1 hectare = 100 ares).

---

## Hectare = hect-are (multiplier hect-are)

- **1 are = 100 m²** (SI-accepted unit of area).
- **1 hectare = 100 ares = 10,000 m²**, i.e. hectare = hecto × are.
- **Implementation:**
  1. **Register "are"** in [unit_registry.rs](crates/snaq-lite-lang/src/unit_registry.rs): Area dimension, factor 100.0, defining_unit `Unit::from_base_unit("m2")` (so 1 are = 100 m²).
  2. **Add prefix "hect"** (hecto, 10²) in [prefix.rs](crates/snaq-lite-lang/src/prefix.rs): add `("hect", Prefix::Metric(2))` to `metric_short_prefixes()`. The array size becomes 21. Prefix list is already sorted by length (longest first) at use site, so "hectare" will resolve as "hect" + "are" → 100 × are = 10,000 m².
  3. **Optional:** Register "hectare" as an explicit alias (e.g. `add_derived_unit("hectare", Area, 100.0, Unit::from_base_unit("are"))`) so that typing "hectare" gives the same quantity and can display as "hectare" instead of "hare". Numerically it remains 100 ares.
  4. **Display note:** If we rely only on prefix resolution, the unit would display as "hare" (h + are). Adding the "hectare" alias gives a friendly display name when the user types "hectare" or "ha".

---

## Area dimension and canonical units (unit_registry.rs)

- Add `reg.dimensions.add_base_dimension("Area");`
- **m2** (canonical): `add_derived_unit("m2", BaseRepresentation::from_base("Area"), 1.0, Unit::from_base_unit("m").powi(2))`
- **are**: `add_derived_unit("are", BaseRepresentation::from_base("Area"), 100.0, Unit::from_base_unit("m2"))`  (1 are = 100 m²)
- **hectare** (optional alias): `add_derived_unit("hectare", ..., 100.0, Unit::from_base_unit("are"))` so 1 hectare = 100 are; then "ha" aliases to hectare
- **km2, cm2, mm2**: Either **(A) explicit** or **(B) prefix with exponent** (see section below). (A) Register as explicit derived units with factors 1e6, 1e-4, 1e-6 and defining_unit m2. (B) Preferable: make the multiplier behave correctly when exponent ≠ 1 so that "km2" resolves to (k·m)² without registering km2 explicitly.
- **inch** (length): 0.0254 m
- **in2** (canonical for square inch): factor (0.0254)², defining_unit inch²
- Optional: **foot**, **ft2**, **square_foot**

---

## Shorthand symbols (aliases)

- **m2:** m² (if lexer accepts), sqm
- **km2, cm2, mm2:** km², cm², mm² if valid
- **are:** (no standard single-letter; "a" is atto)
- **hectare:** ha
- **inch:** in
- **in2:** in², sqin
- **ft2:** ft², sqft (if foot added)

---

## No-underscore names (aliases)

- **squaremeter**, **square_meter** → m2
- **squarekilometer**, **square_kilometer** → km2
- **squarecentimeter**, **square_centimeter** → cm2
- **squaremillimeter**, **square_millimeter** → mm2
- **squareinch**, **square_inch** → in2
- **squarefoot**, **square_foot** → ft2 (if added)

Plurals (squaremeters, squareinches, etc.) handled by existing singularization.

---

## Prefix change (prefix.rs)

- Extend `metric_short_prefixes()` from 20 to 21 entries and add `("hect", Prefix::Metric(2))` so that "hectare" parses as hect + are. Keep ("h", Prefix::Metric(2)) for other units (e.g. hectare could also be resolved via "h" + "ectare" if "ectare" were a unit—it isn’t; so "hect" must be in the list for "hectare" → "hect" + "are").

---

## Squared-unit conversion (m² ↔ km², cm², mm²)

- **Rule:** For length L with 1 L = k m, area L² has 1 L² = k² m². Conversion already uses the exponent: `to_base_unit_representation` does `prefix_factor.powf(exp_f64)`, so a unit (prefix·m)^2 gets factor 1000² for kilo.
- **Two approaches:**

  **A) Explicit units**  
  Register km2, cm2, mm2 with factors 1e6, 1e-4, 1e-6. Exact match so "km2" never parsed as k×m2 (which would wrongly give 1000 m²).

  **B) Multiplier behaves with exponent (preferred)**  
  Do **not** treat "km2" as prefix "k" + unit "m2" (that would give 1000 m²). Instead, in `try_lookup` (or equivalent), when the part after the prefix is a **squared-length form** ("m2", "m²"), resolve to **(prefix × base_length)^2**:
  - "km2" → prefix "k" + rest "m2" → unit = `get_unit("m").with_prefix(k).powi(2)` → (km)² → 1000² m².
  - "cm2" → prefix "c" + "m2" → (cm)² → 1e-4 m².
  - "mm2" → prefix "m" (milli) + "m2" → (mm)² → 1e-6 m² (longest prefix first so "mm" is not used as prefix for "m2"; we need "m" + "m2" → milli·m with exponent 2).

  Implementation: after splitting `ident = prefix_symbol + rest`, if `rest` is one of a fixed set of squared-length names (e.g. "m2", "m²"), look up the underlying length unit "m", return `get_unit("m").with_prefix(prefix).powi(2)`. No need to register km2, cm2, mm2; conversion is correct because the stored unit has exponent 2 and the existing formula applies it to the prefix factor. With option B, only "m2" (and aliases) are registered for area; all prefixed squared forms (km2, cm2, mm2, etc.) follow from prefix + squared-length rule.

- **Compound (e.g. 1 km * 1 km):** Already correct: unit (km)² has one factor (m, kilo, 2), so `to_base_unit_representation` gives 1000² m². No change.
- **Tests (mandatory):**
  - `1 km2 as m2` → 1e6
  - `1 m2 as km2` → 1e-6
  - `1 cm2 as m2` → 1e-4
  - `1 mm2 as m2` → 1e-6
  - `1 km * 1 km` same dimension as m2 and converts to 1e6 m2 when value is 1

---

## Tests

- Area dimension and same_dimension(m2, m*m), same_dimension(hectare, are) with appropriate factors
- 1 are = 100 m²; 1 hectare = 100 are = 10,000 m²
- "hectare" resolves (via hect+are or via alias) to 10,000 m²
- Parsing: 1 m2, 1 squaremeter, 1 squareinch, 1 ha, 1 hectare, 1 are
- **Squared-unit conversion:** 1 km2 as m2 = 1e6; 1 m2 as km2 = 1e-6; 1 cm2 as m2 = 1e-4; 1 mm2 as m2 = 1e-6; 1 km * 1 km converts to 1e6 m2
- Unsupported list: remove "inch" if added
- Every new unit/alias parses as `1 <name>`

---

## Documentation

- README / memory: Area dimension; are (100 m²); hectare = 100 ares (hect-are); shorthand (m2, ha, in2) and no-underscore (squaremeter, squareinch).
