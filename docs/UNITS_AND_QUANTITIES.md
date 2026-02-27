# Units and quantities

This document describes how quantity literals, unit expressions, and unit conversion work in the language. It does not describe how units are stored or resolved internally.

## Quantity literals

A **quantity** is a number with an optional unit. You can write:

- **Number followed by one or more unit/constant identifiers:** e.g. `100 m`, `2 pi rad`, `1 s`. The number and identifiers are combined with implicit multiplication (see [SYNTAX.md](SYNTAX.md)). Identifiers are resolved as units (e.g. `m`, `rad`) or symbols (e.g. `pi`); all must be compatible (same dimension for units in the same term).
- **Bare unit:** e.g. `hour`, `rad`. This denotes **1** in that unit (1 hour, 1 radian).

Plural unit names (e.g. `meters`, `seconds`, `kilometers`) are accepted and normalized to the canonical singular form (e.g. `meter`, `second`, `kilometer`).

## Unit expressions

Unit expressions are built from **identifiers** combined with:

- **`*`** — product (e.g. `newton * meter`)
- **`/`** or **`per`** — division (e.g. `m / s`, `meters per second`)

They appear:

- Inside quantity literals (e.g. `100 km / hour`).
- As the right-hand side of **unit conversion** (see below).

Only unit-like identifiers (and no plain numbers or symbols) are allowed in a **unit-only** expression used after `as`.

## Unit conversion

**Syntax:** `expression as unit_term`

Examples: `10 km as m`, `10 km per hour as m / s`, `180 degree as rad`.

- The left-hand side is any expression (typically a quantity).
- The right-hand side is a **unit-only** expression (identifiers with `*`, `/`, `per`).
- **Semantics:** The value of the left side is converted to the dimension and unit given on the right. The **dimension** of the left value and the right unit must match; otherwise the runtime reports a dimension mismatch.

## Prefixes

Metric (and other) **prefixes** can be applied to units. For example:

- **k** (kilo): `km` = kilometer, `kg` = kilogram
- **m** (milli): `mm` = millimeter, `ms` = millisecond
- **µ** (micro): `µm` = micrometer, `µs` = microsecond
- **c** (centi): `cm` = centimeter
- **d** (deci): `dm` = decimeter
- **M** (mega), **G** (giga), **n** (nano), etc.

The language resolves the longest matching prefix plus unit name. So `km` is one unit (kilometer), not `k` × `m`. Squared-length units like `km2` or `km²` are interpreted as (kilometer)², so area conversion works correctly (e.g. km² to m²).

## Plural and singular forms

Unit names can be written in **plural** form (e.g. `meters`, `seconds`, `kilometers`). They are normalized to the **singular** form used in the unit registry. Both forms refer to the same unit; display may show the canonical singular form.

## Supported units (overview)

The default environment provides units in these categories (non-exhaustive list):

- **SI base:** m, kg, s, A, K, mol, cd (and long forms: meter, kilogram, second, ampere, kelvin, mole, candela).
- **SI derived with special names:** J, C, V, F, ohm, S, Wb, T, H, Hz, N, Pa, W, lm, lx, Bq, Gy, Sv, kat (and long forms: joule, coulomb, volt, farad, etc.).
- **Time:** second, minute, hour, day, week, month, quarter, year, decade, century, millennium (and plurals).
- **Length:** meter, km, mile, au, parsec, light_year, nautical_mile (nmi), inch (in), foot (ft).
- **Angle:** rad (radian), degree (degrees), arcmin (arcminute), arcsec (arcsecond).
- **Area:** m² (m2, sqm, squaremeter, etc.), km², cm², mm², are, hectare (ha), in², ft², squareinch, squarefoot, etc.
- **Volume:** m³ (m3, cubicmeter), km³, cm³, mm³, liter (litre, L), milliliter (ml, mL).
- **Energy:** joule, eV, calorie, kcal, BTU, Wh, kWh.
- **Power:** W, horsepower (hp).
- **Pressure:** Pa (pascal), bar, atm, psi, mmHg, torr.
- **Mass:** kg, g (gram), pound (lb), ounce (oz).
- **Temperature:** kelvin, celsius, fahrenheit.
- **Concentration:** molar (M), mol/L.
- **Dimensionless ratios:** percent, ppm, ppb (use `percent`; `%` is the modulo operator).
- **Velocity:** knot (nautical mile per hour); also compound units like m/s, km/hour.
- **Solid angle:** steradian, sr (dimensionless, factor 1).
- **Other:** Various other SI-derived and common units.

### Temperature (Fahrenheit)

Fahrenheit uses a scale factor of 5/9 relative to kelvin so that **temperature differences** convert correctly (e.g. 9 fahrenheit as K → 5). The absolute zero-point (32°F = 0°C) is not modeled; for absolute temperature conversion between °F and °C or K you need to apply the offset yourself (e.g. in formulas) or use a future affine-unit feature.

If you use an identifier that is not registered as a unit and not bound as a variable or symbol, the behaviour depends on context (e.g. it may be treated as a symbol or produce an unknown-unit error when used in a unit position). See [SYMBOLS.md](SYMBOLS.md) and [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md).

## See also

- [SYNTAX.md](SYNTAX.md) — implicit multiplication and `as` / `per`
- [LITERALS_AND_VALUES.md](LITERALS_AND_VALUES.md) — value types
- [SYMBOLS.md](SYMBOLS.md) — how identifiers resolve (variable, unit, symbol)
- [ERRORS_AND_EDGE_CASES.md](ERRORS_AND_EDGE_CASES.md) — unknown unit, dimension mismatch
- [README.md](README.md) — language overview and index
