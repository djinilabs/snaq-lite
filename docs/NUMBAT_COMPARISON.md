# Numbat vs snaq-lite unit handling comparison

Comparison based on Numbat source (sharkdp/numbat: quantity.rs, unit.rs, dimension.rs).

## Differences

### 1. **Common-factor optimization in `convert_to`** (Numbat has it, we did not)
- **Numbat:** When converting e.g. km/h to mile/h, removes the common "per hour" factor and only converts the length part. Reduces unnecessary conversion steps and improves commutativity (see [numbat#118](https://github.com/sharkdp/numbat/issues/118)).
- **snaq-lite:** Always converts via full base representation (self_factor / target_factor).
- **Status:** Implemented below.

### 2. **`full_simplify` heuristics** (Numbat has 3, we had 1)
- **Numbat:** (1) Dimensionless → scalar [we had this]. (2) Try `is_multiple_of(unit, factor_unit)` to simplify compound units to a power of one factor. (3) Scalar-like units: e.g. `3% · kg` → `0.03 kg` (group factors that are dimensionally scalar, fold into value).
- **snaq-lite:** Only (1).
- **Status:** (2) and (3) not implemented; would require `is_multiple_of` and factor grouping.

### 3. **`full_simplify_with_registry` semantics** (Numbat: definitional match)
- **Numbat:** Only simplifies to a derived unit when conversion factor to base **matches** (definitionally equivalent, e.g. J/s = W). Does not simplify when only dimension matches (e.g. Wh/W ≠ century).
- **snaq-lite:** Picked any same-dimension unit with value in [0.1, 1000], which could choose a wrong unit.
- **Status:** Implemented below: require factor match and prefer fewer factors.

### 4. **AcceptsPrefix per unit** (Numbat has it)
- **Numbat:** Each unit declares `AcceptsPrefix`: none, short only, long only, both. Prefix parser respects this.
- **snaq-lite:** We try all metric short prefixes on any unit; no per-unit policy.
- **Status:** Not implemented; would require extending `UnitDefinition` and prefix resolution.

### 5. **Display: conversion target** (Numbat has it)
- **Numbat:** `with_conversion_target` / `conversion_target`: display as `8 × 45 min` instead of `360 min` for conversion results.
- **snaq-lite:** We always display as `value unit`.
- **Status:** Not implemented.

### 6. **`can_simplify` flag** (Numbat has it)
- **Numbat:** Quantity can be marked `can_simplify: false` to disable simplification.
- **snaq-lite:** No flag.
- **Status:** Not implemented.

### 7. **Unit definition location** (architectural)
- **Numbat:** Unit carries its definition (Base vs Derived) in `UnitIdentifier`; `Unit::to_base_unit_representation()` is on the unit.
- **snaq-lite:** Definitions live in registry only; `to_base_unit_representation(unit, registry)` requires registry. By design.

### 8. **Registry: get_matching_unit_names** (Numbat has it)
- **Numbat:** Registry can return unit names by dimension/base representation.
- **snaq-lite:** We iterate `unit_names()` and filter by `same_dimension`.
- **Status:** Acceptable; we do not add dimension index.

---

## Implemented in this pass

- **Common-factor optimization in `convert_to`**: compute common factors between self.unit and target, reduce both, convert reduced units; if same dimension, result = value × self_red_factor / target_red_factor in target unit.
- **`full_simplify_with_registry`**: only consider a candidate unit if its conversion factor to base matches the current unit’s factor (within tolerance); prefer fewer factors (simpler unit).
