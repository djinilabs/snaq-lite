//! Unit registry: base and derived units, resolution to base representation.
//! Supports prefix parsing (e.g. "km" → kilo × meter) and squared-length resolution
//! (e.g. "km2" or "km²" → (kilo·meter)² = 10⁶ m²) so prefixed area units convert correctly.
//! Plural unit names (e.g. "meters") are normalized to singular before lookup.

use crate::dimension::{BaseRepresentation, DimensionRegistry};
use crate::prefix::{self, Prefix};
use crate::unit::{Unit, UnitFactor};
use singularize::singularize;
use std::collections::HashMap;

/// Definition of a unit: either base (fundamental) or derived from another unit.
#[derive(Clone, Debug)]
pub enum UnitDefinition {
    Base {
        dimension: BaseRepresentation,
    },
    Derived {
        dimension: BaseRepresentation,
        factor: f64,
        defining_unit: Unit,
    },
}

/// Registry mapping unit names to definitions and dimensions.
#[derive(Clone)]
pub struct UnitRegistry {
    pub dimensions: DimensionRegistry,
    units: HashMap<String, UnitDefinition>,
}

impl UnitRegistry {
    pub fn new() -> Self {
        Self {
            dimensions: DimensionRegistry::new(),
            units: HashMap::new(),
        }
    }

    pub fn add_base_unit(&mut self, name: &str, dimension: BaseRepresentation) {
        self.units.insert(
            name.to_string(),
            UnitDefinition::Base {
                dimension: dimension.clone(),
            },
        );
        // Ensure dimension name exists in dimension registry if it's a single base
        for (dim_name, _) in dimension.iter() {
            if !self.dimensions.contains(dim_name) {
                self.dimensions.add_base_dimension(dim_name);
            }
        }
    }

    pub fn add_derived_unit(
        &mut self,
        name: &str,
        dimension: BaseRepresentation,
        factor: f64,
        defining_unit: Unit,
    ) {
        self.units.insert(
            name.to_string(),
            UnitDefinition::Derived {
                dimension,
                factor,
                defining_unit,
            },
        );
    }

    pub fn get(&self, name: &str) -> Option<&UnitDefinition> {
        self.units.get(name)
    }

    /// Return the Unit for a registered unit name (base or derived). Used for resolution.
    pub fn get_unit(&self, name: &str) -> Option<Unit> {
        self.units.get(name).map(|_| Unit::from_base_unit(name))
    }

    /// Squared-length rest names: when prefix + rest is parsed and rest is one of these,
    /// resolve to (prefix × base length)² so that e.g. km2 → (k·m)² = 10⁶ m².
    const SQUARED_LENGTH_REST: &[&str] = &["m2", "m²"];

    /// Cubed-length rest names: when prefix + rest is parsed and rest is one of these,
    /// resolve to (prefix × base length)³ so that e.g. km3 → (k·m)³ = 10⁹ m³.
    const CUBED_LENGTH_REST: &[&str] = &["m3", "m³"];

    /// Try to resolve an identifier to a Unit: exact match first, then prefix + base (e.g. "km" → kilo×m).
    /// When rest is a squared-length form (e.g. "m2", "m²"), returns (prefix × base length)² so conversion is correct.
    /// When rest is a cubed-length form (e.g. "m3", "m³"), returns (prefix × base length)³ for volume.
    /// Prefix list must be sorted longest-first (so "Mm" → mega×m, not milli×"m").
    fn try_lookup(
        &self,
        ident: &str,
        prefixes_by_len: &[&(&str, Prefix)],
    ) -> Option<Unit> {
        if self.units.contains_key(ident) {
            return self.get_unit(ident);
        }
        for (symbol, p) in prefixes_by_len {
            if ident.len() > symbol.len() && ident.starts_with(*symbol) {
                let rest = &ident[symbol.len()..];
                // Squared-length: rest "m2" or "m²" → (prefix·m)² so km2, cm2, mm2 convert correctly
                if Self::SQUARED_LENGTH_REST.contains(&rest) && self.units.contains_key("m") {
                    let u = self.get_unit("m").unwrap();
                    return Some(u.with_prefix(*p).powi(2));
                }
                // Cubed-length: rest "m3" or "m³" → (prefix·m)³ so km3, cm3, mm3 convert correctly
                if Self::CUBED_LENGTH_REST.contains(&rest) && self.units.contains_key("m") {
                    let u = self.get_unit("m").unwrap();
                    return Some(u.with_prefix(*p).powi(3));
                }
                if self.units.contains_key(rest) {
                    let u = self.get_unit(rest).unwrap();
                    return Some(u.with_prefix(*p));
                }
            }
        }
        None
    }

    /// Resolve identifier to Unit: exact name first, then prefix + base unit (e.g. "km" → kilo×m).
    /// If not found, singularize the identifier and try again (e.g. "meters" → "meter").
    /// The returned Unit always uses the canonical (singular) registry key for display/storage.
    /// Prefixes tried longest-first so "Mm" → mega×m not milli×"m" (invalid).
    pub fn get_unit_with_prefix(&self, ident: &str) -> Option<Unit> {
        let prefixes = prefix::metric_short_prefixes();
        let mut by_len: Vec<_> = prefixes.iter().collect();
        by_len.sort_by_key(|(s, _)| std::cmp::Reverse(s.len()));
        if let Some(u) = self.try_lookup(ident, &by_len) {
            return Some(u);
        }
        let canonical = singularize(ident);
        if canonical != ident {
            if let Some(u) = self.try_lookup(&canonical, &by_len) {
                return Some(u);
            }
        }
        None
    }

    /// Express this unit as (base unit product, numeric conversion factor).
    pub fn to_base_unit_representation(&self, unit: &Unit) -> Option<(Unit, f64)> {
        let mut result_unit = Unit::scalar();
        let mut result_factor = 1.0_f64;

        for f in unit.iter() {
            let def = self.get(&f.unit_name)?;
            let prefix_factor = f.prefix.factor();
            let exp_f64 = (*f.exponent.numer() as f64) / (*f.exponent.denom() as f64);

            match def {
                UnitDefinition::Base { .. } => {
                    result_unit = result_unit.mul(&Unit::from_factor(UnitFactor::new(
                        f.unit_name.clone(),
                        Prefix::none(),
                        f.exponent,
                    )));
                    result_factor *= prefix_factor.powf(exp_f64);
                }
                UnitDefinition::Derived {
                    factor,
                    defining_unit,
                    ..
                } => {
                    let (base_u, def_base_factor) =
                        self.to_base_unit_representation(defining_unit)?;
                    result_unit = result_unit.mul(&base_u.power(f.exponent));
                    // Include defining unit's factor so e.g. degrees -> degree -> π/180 rad
                    result_factor *= (prefix_factor * factor * def_base_factor).powf(exp_f64);
                }
            }
        }

        Some((result_unit, result_factor))
    }

    /// Names of all registered units (for simplification / preferred unit lookup).
    pub fn unit_names(&self) -> impl Iterator<Item = &String> {
        self.units.keys()
    }

    /// Two units have the same dimension if their base representations (ignoring factor) match.
    pub fn same_dimension(&self, a: &Unit, b: &Unit) -> Option<bool> {
        let (u1, _) = self.to_base_unit_representation(a)?;
        let (u2, _) = self.to_base_unit_representation(b)?;
        // Compare canonical form: same factor names and exponents.
        if u1.iter().count() != u2.iter().count() {
            return Some(false);
        }
        let mut v1: Vec<_> = u1.iter().map(|f| (f.unit_name.as_str(), f.exponent)).collect();
        let mut v2: Vec<_> = u2.iter().map(|f| (f.unit_name.as_str(), f.exponent)).collect();
        v1.sort_by_key(|(n, _)| *n);
        v2.sort_by_key(|(n, _)| *n);
        Some(v1 == v2)
    }
}

impl Default for UnitRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper: register a derived unit that is a 1:1 alias of an existing unit (same dimension).
fn add_derived_alias(
    reg: &mut UnitRegistry,
    name: &str,
    dimension: &str,
    ref_unit: Unit,
) {
    reg.add_derived_unit(
        name,
        BaseRepresentation::from_base(dimension),
        1.0,
        ref_unit,
    );
}

/// Build default registry with full SI base units, key SI derived units, and Numbat-parity units.
///
/// **SI base (7):** m (length), kg (mass), s (time), A (current), K (temperature), mol (amount), cd (luminous intensity).
/// **SI derived (with special names):** J, C, V, F, ohm, S, Wb, T, H, Hz, N, Pa, W, lm, lx, Bq, Gy, Sv, kat; km, g, hour, minute, second, day, week, month, quarter, year, decade, century, millennium; plus mile, au, parsec, light_year, eV, celsius. Plural input (e.g. "meters") is normalized to singular before lookup.
pub fn default_si_registry() -> UnitRegistry {
    let mut reg = UnitRegistry::new();

    reg.dimensions.add_base_dimension("Length");
    reg.dimensions.add_base_dimension("Time");
    reg.dimensions.add_base_dimension("Mass");
    reg.dimensions.add_base_dimension("Current");
    reg.dimensions.add_base_dimension("Temperature");
    reg.dimensions.add_base_dimension("AmountOfSubstance");
    reg.dimensions.add_base_dimension("LuminousIntensity");
    reg.dimensions.add_base_dimension("Energy");
    reg.dimensions.add_base_dimension("Angle");

    // SI base units (7) + rad (Angle)
    reg.add_base_unit("m", BaseRepresentation::from_base("Length"));
    reg.add_base_unit("kg", BaseRepresentation::from_base("Mass"));
    reg.add_base_unit("s", BaseRepresentation::from_base("Time"));
    reg.add_base_unit("A", BaseRepresentation::from_base("Current"));
    reg.add_base_unit("K", BaseRepresentation::from_base("Temperature"));
    reg.add_base_unit("mol", BaseRepresentation::from_base("AmountOfSubstance"));
    reg.add_base_unit("cd", BaseRepresentation::from_base("LuminousIntensity"));
    reg.add_base_unit("rad", BaseRepresentation::from_base("Angle")); // Angle base unit (SI coherent)
    add_derived_alias(&mut reg, "ampere", "Current", Unit::from_base_unit("A"));
    add_derived_alias(&mut reg, "kelvin", "Temperature", Unit::from_base_unit("K"));
    add_derived_alias(&mut reg, "mole", "AmountOfSubstance", Unit::from_base_unit("mol"));
    add_derived_alias(&mut reg, "candela", "LuminousIntensity", Unit::from_base_unit("cd"));

    // Angle: rad (base), degree = π/180 rad, arcmin = 1/60 degree, arcsec = 1/3600 degree
    reg.add_derived_unit(
        "degree",
        BaseRepresentation::from_base("Angle"),
        std::f64::consts::PI / 180.0,
        Unit::from_base_unit("rad"),
    );
    reg.add_derived_unit(
        "arcmin",
        BaseRepresentation::from_base("Angle"),
        1.0 / 60.0,
        Unit::from_base_unit("degree"),
    );
    add_derived_alias(&mut reg, "arcminute", "Angle", Unit::from_base_unit("arcmin"));
    reg.add_derived_unit(
        "arcsec",
        BaseRepresentation::from_base("Angle"),
        1.0 / 3600.0,
        Unit::from_base_unit("degree"),
    );
    add_derived_alias(&mut reg, "arcsecond", "Angle", Unit::from_base_unit("arcsec"));
    // Length: SI derived + Numbat parity (with long-form aliases)
    reg.add_derived_unit(
        "meter",
        BaseRepresentation::from_base("Length"),
        1.0,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "km",
        BaseRepresentation::from_base("Length"),
        1000.0,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "kilometer",
        BaseRepresentation::from_base("Length"),
        1000.0,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "mile",
        BaseRepresentation::from_base("Length"),
        1609.344,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "au",
        BaseRepresentation::from_base("Length"),
        149_597_870_700.0,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "parsec",
        BaseRepresentation::from_base("Length"),
        3.085_677_581_491_367e16,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "light_year",
        BaseRepresentation::from_base("Length"),
        9.460_730_472_580_8e15,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "nautical_mile",
        BaseRepresentation::from_base("Length"),
        1852.0,
        Unit::from_base_unit("m"),
    );
    add_derived_alias(&mut reg, "nmi", "Length", Unit::from_base_unit("nautical_mile"));

    // Area: m² (canonical), are = 100 m², hectare = 100 are. km2/cm2/mm2 resolved via prefix + m2 → (prefix·m)².
    reg.dimensions.add_base_dimension("Area");
    reg.add_derived_unit(
        "m2",
        BaseRepresentation::from_base("Area"),
        1.0,
        Unit::from_base_unit("m").powi(2),
    );
    reg.add_derived_unit(
        "are",
        BaseRepresentation::from_base("Area"),
        100.0,
        Unit::from_base_unit("m2"),
    );
    reg.add_derived_unit(
        "hectare",
        BaseRepresentation::from_base("Area"),
        100.0,
        Unit::from_base_unit("are"),
    );
    add_derived_alias(&mut reg, "ha", "Area", Unit::from_base_unit("hectare"));
    add_derived_alias(&mut reg, "m²", "Area", Unit::from_base_unit("m2"));
    add_derived_alias(&mut reg, "sqm", "Area", Unit::from_base_unit("m2"));
    add_derived_alias(&mut reg, "squaremeter", "Area", Unit::from_base_unit("m2"));
    add_derived_alias(&mut reg, "square_meter", "Area", Unit::from_base_unit("m2"));
    add_derived_alias(&mut reg, "squarekilometer", "Area", Unit::from_base_unit("m").with_prefix(Prefix::Metric(3)).powi(2));
    add_derived_alias(&mut reg, "square_kilometer", "Area", Unit::from_base_unit("m").with_prefix(Prefix::Metric(3)).powi(2));
    add_derived_alias(&mut reg, "squarecentimeter", "Area", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-2)).powi(2));
    add_derived_alias(&mut reg, "square_centimeter", "Area", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-2)).powi(2));
    add_derived_alias(&mut reg, "squaremillimeter", "Area", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-3)).powi(2));
    add_derived_alias(&mut reg, "square_millimeter", "Area", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-3)).powi(2));

    // Length: inch and foot (for area in2, ft2)
    const INCH_TO_M: f64 = 0.0254;
    const FOOT_TO_M: f64 = 0.3048;
    reg.add_derived_unit(
        "inch",
        BaseRepresentation::from_base("Length"),
        INCH_TO_M,
        Unit::from_base_unit("m"),
    );
    add_derived_alias(&mut reg, "in", "Length", Unit::from_base_unit("inch"));
    reg.add_derived_unit(
        "foot",
        BaseRepresentation::from_base("Length"),
        FOOT_TO_M,
        Unit::from_base_unit("m"),
    );
    add_derived_alias(&mut reg, "ft", "Length", Unit::from_base_unit("foot"));
    // Area: square inch, square foot
    reg.add_derived_unit(
        "in2",
        BaseRepresentation::from_base("Area"),
        INCH_TO_M * INCH_TO_M,
        Unit::from_base_unit("inch").powi(2),
    );
    add_derived_alias(&mut reg, "in²", "Area", Unit::from_base_unit("in2"));
    add_derived_alias(&mut reg, "sqin", "Area", Unit::from_base_unit("in2"));
    add_derived_alias(&mut reg, "squareinch", "Area", Unit::from_base_unit("in2"));
    add_derived_alias(&mut reg, "square_inch", "Area", Unit::from_base_unit("in2"));
    reg.add_derived_unit(
        "ft2",
        BaseRepresentation::from_base("Area"),
        FOOT_TO_M * FOOT_TO_M,
        Unit::from_base_unit("foot").powi(2),
    );
    add_derived_alias(&mut reg, "sqft", "Area", Unit::from_base_unit("ft2"));
    add_derived_alias(&mut reg, "squarefoot", "Area", Unit::from_base_unit("ft2"));
    add_derived_alias(&mut reg, "square_foot", "Area", Unit::from_base_unit("ft2"));

    // Volume: m³ (canonical), liter = 10⁻³ m³, milliliter = 10⁻⁶ m³. km3/cm3/mm3 resolved via prefix + m3 → (prefix·m)³.
    reg.dimensions.add_base_dimension("Volume");
    reg.add_derived_unit(
        "m3",
        BaseRepresentation::from_base("Volume"),
        1.0,
        Unit::from_base_unit("m").powi(3),
    );
    add_derived_alias(&mut reg, "m³", "Volume", Unit::from_base_unit("m3"));
    add_derived_alias(&mut reg, "cubicmeter", "Volume", Unit::from_base_unit("m3"));
    add_derived_alias(&mut reg, "cubic_meter", "Volume", Unit::from_base_unit("m3"));
    add_derived_alias(&mut reg, "cubickilometer", "Volume", Unit::from_base_unit("m").with_prefix(Prefix::Metric(3)).powi(3));
    add_derived_alias(&mut reg, "cubic_kilometer", "Volume", Unit::from_base_unit("m").with_prefix(Prefix::Metric(3)).powi(3));
    add_derived_alias(&mut reg, "cubiccentimeter", "Volume", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-2)).powi(3));
    add_derived_alias(&mut reg, "cubic_centimeter", "Volume", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-2)).powi(3));
    add_derived_alias(&mut reg, "cubicmillimeter", "Volume", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-3)).powi(3));
    add_derived_alias(&mut reg, "cubic_millimeter", "Volume", Unit::from_base_unit("m").with_prefix(Prefix::Metric(-3)).powi(3));
    reg.add_derived_unit(
        "liter",
        BaseRepresentation::from_base("Volume"),
        0.001,
        Unit::from_base_unit("m3"),
    );
    add_derived_alias(&mut reg, "litre", "Volume", Unit::from_base_unit("liter"));
    add_derived_alias(&mut reg, "L", "Volume", Unit::from_base_unit("liter"));
    reg.add_derived_unit(
        "milliliter",
        BaseRepresentation::from_base("Volume"),
        0.001,
        Unit::from_base_unit("liter"),
    );
    add_derived_alias(&mut reg, "ml", "Volume", Unit::from_base_unit("milliliter"));
    add_derived_alias(&mut reg, "mL", "Volume", Unit::from_base_unit("milliliter"));

    // Time: SI derived. Calendar-style durations use Julian year (365.25 days) for a fixed definition.
    const HOURS_PER_DAY: f64 = 24.0;
    const DAYS_PER_WEEK: f64 = 7.0;
    const DAYS_PER_YEAR_JULIAN: f64 = 365.25;
    reg.add_derived_unit(
        "hour",
        BaseRepresentation::from_base("Time"),
        3600.0,
        Unit::from_base_unit("s"),
    );
    reg.add_derived_unit(
        "minute",
        BaseRepresentation::from_base("Time"),
        60.0,
        Unit::from_base_unit("s"),
    );
    reg.add_derived_unit(
        "second",
        BaseRepresentation::from_base("Time"),
        1.0,
        Unit::from_base_unit("s"),
    );
    reg.add_derived_unit(
        "day",
        BaseRepresentation::from_base("Time"),
        HOURS_PER_DAY,
        Unit::from_base_unit("hour"),
    );
    reg.add_derived_unit(
        "week",
        BaseRepresentation::from_base("Time"),
        DAYS_PER_WEEK,
        Unit::from_base_unit("day"),
    );
    reg.add_derived_unit(
        "year",
        BaseRepresentation::from_base("Time"),
        DAYS_PER_YEAR_JULIAN,
        Unit::from_base_unit("day"),
    );
    reg.add_derived_unit(
        "month",
        BaseRepresentation::from_base("Time"),
        1.0 / 12.0,
        Unit::from_base_unit("year"),
    );
    reg.add_derived_unit(
        "quarter",
        BaseRepresentation::from_base("Time"),
        1.0 / 4.0,
        Unit::from_base_unit("year"),
    );
    reg.add_derived_unit(
        "decade",
        BaseRepresentation::from_base("Time"),
        10.0,
        Unit::from_base_unit("year"),
    );
    reg.add_derived_unit(
        "century",
        BaseRepresentation::from_base("Time"),
        100.0,
        Unit::from_base_unit("year"),
    );
    reg.add_derived_unit(
        "millennium",
        BaseRepresentation::from_base("Time"),
        1000.0,
        Unit::from_base_unit("year"),
    );
    reg.dimensions.add_base_dimension("Frequency");
    reg.add_derived_unit(
        "Hz",
        BaseRepresentation::from_base("Frequency"),
        1.0,
        Unit::from_base_unit("s").powi(-1),
    );

    // Velocity: knot = 1 nautical mile per hour = 1852/3600 m/s
    reg.dimensions.add_base_dimension("Velocity");
    reg.add_derived_unit(
        "knot",
        BaseRepresentation::from_base("Velocity"),
        1852.0 / 3600.0,
        Unit::from_base_unit("m").div(&Unit::from_base_unit("s")),
    );

    // Mass: SI derived (gram)
    reg.add_derived_unit(
        "g",
        BaseRepresentation::from_base("Mass"),
        0.001,
        Unit::from_base_unit("kg"),
    );
    add_derived_alias(&mut reg, "gram", "Mass", Unit::from_base_unit("g"));
    // Mass (imperial/US): pound = 0.45359237 kg, ounce = 1/16 lb
    const LB_TO_KG: f64 = 0.45359237;
    reg.add_derived_unit(
        "pound",
        BaseRepresentation::from_base("Mass"),
        LB_TO_KG,
        Unit::from_base_unit("kg"),
    );
    add_derived_alias(&mut reg, "lb", "Mass", Unit::from_base_unit("pound"));
    reg.add_derived_unit(
        "ounce",
        BaseRepresentation::from_base("Mass"),
        LB_TO_KG / 16.0,
        Unit::from_base_unit("kg"),
    );
    add_derived_alias(&mut reg, "oz", "Mass", Unit::from_base_unit("ounce"));

    // Energy: joule = kg·m²/s², eV = 1.602176634e-19 J
    let joule_unit = Unit::from_base_unit("kg")
        .mul(&Unit::from_base_unit("m").powi(2))
        .div(&Unit::from_base_unit("s").powi(2));
    reg.add_derived_unit(
        "joule",
        BaseRepresentation::from_base("Energy"),
        1.0,
        joule_unit,
    );
    reg.add_derived_unit(
        "eV",
        BaseRepresentation::from_base("Energy"),
        1.602_176_634e-19,
        Unit::from_base_unit("joule"),
    );
    // Energy (non-SI): calorie = 4.184 J, kcal, BTU, Wh, kWh
    reg.add_derived_unit(
        "calorie",
        BaseRepresentation::from_base("Energy"),
        4.184,
        Unit::from_base_unit("joule"),
    );
    reg.add_derived_unit(
        "kcal",
        BaseRepresentation::from_base("Energy"),
        4184.0,
        Unit::from_base_unit("joule"),
    );
    reg.add_derived_unit(
        "BTU",
        BaseRepresentation::from_base("Energy"),
        1055.06,
        Unit::from_base_unit("joule"),
    );
    reg.add_derived_unit(
        "Wh",
        BaseRepresentation::from_base("Energy"),
        3600.0,
        Unit::from_base_unit("joule"),
    );
    reg.add_derived_unit(
        "kWh",
        BaseRepresentation::from_base("Energy"),
        3_600_000.0,
        Unit::from_base_unit("joule"),
    );

    // Force: N = kg·m/s²
    reg.dimensions.add_base_dimension("Force");
    let newton_unit = Unit::from_base_unit("kg")
        .mul(&Unit::from_base_unit("m"))
        .div(&Unit::from_base_unit("s").powi(2));
    reg.add_derived_unit(
        "N",
        BaseRepresentation::from_base("Force"),
        1.0,
        newton_unit,
    );
    add_derived_alias(&mut reg, "newton", "Force", Unit::from_base_unit("N"));

    // Pressure: Pa = N/m²
    reg.dimensions.add_base_dimension("Pressure");
    reg.add_derived_unit(
        "Pa",
        BaseRepresentation::from_base("Pressure"),
        1.0,
        Unit::from_base_unit("N").div(&Unit::from_base_unit("m").powi(2)),
    );
    add_derived_alias(&mut reg, "pascal", "Pressure", Unit::from_base_unit("Pa"));
    // Pressure (non-SI): bar = 10⁵ Pa, atm ≈ 101325 Pa, psi, mmHg, torr
    reg.add_derived_unit(
        "bar",
        BaseRepresentation::from_base("Pressure"),
        100_000.0,
        Unit::from_base_unit("Pa"),
    );
    reg.add_derived_unit(
        "atm",
        BaseRepresentation::from_base("Pressure"),
        101_325.0,
        Unit::from_base_unit("Pa"),
    );
    reg.add_derived_unit(
        "psi",
        BaseRepresentation::from_base("Pressure"),
        6894.757293168,
        Unit::from_base_unit("Pa"),
    );
    reg.add_derived_unit(
        "mmHg",
        BaseRepresentation::from_base("Pressure"),
        133.322387415,
        Unit::from_base_unit("Pa"),
    );
    add_derived_alias(&mut reg, "torr", "Pressure", Unit::from_base_unit("mmHg"));

    // Power: W = J/s
    reg.dimensions.add_base_dimension("Power");
    reg.add_derived_unit(
        "W",
        BaseRepresentation::from_base("Power"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("s")),
    );
    reg.add_derived_unit(
        "horsepower",
        BaseRepresentation::from_base("Power"),
        745.7,
        Unit::from_base_unit("W"),
    );
    add_derived_alias(&mut reg, "hp", "Power", Unit::from_base_unit("horsepower"));
    reg.add_derived_unit(
        "J",
        BaseRepresentation::from_base("Energy"),
        1.0,
        Unit::from_base_unit("joule"),
    );

    // Electric charge: C = A·s
    reg.dimensions.add_base_dimension("ElectricCharge");
    reg.add_derived_unit(
        "C",
        BaseRepresentation::from_base("ElectricCharge"),
        1.0,
        Unit::from_base_unit("A").mul(&Unit::from_base_unit("s")),
    );
    add_derived_alias(&mut reg, "coulomb", "ElectricCharge", Unit::from_base_unit("C"));

    // Voltage: V = J/C = W/A
    reg.dimensions.add_base_dimension("Voltage");
    reg.add_derived_unit(
        "V",
        BaseRepresentation::from_base("Voltage"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("C")),
    );
    add_derived_alias(&mut reg, "volt", "Voltage", Unit::from_base_unit("V"));

    // Capacitance: F = C/V
    reg.dimensions.add_base_dimension("Capacitance");
    reg.add_derived_unit(
        "F",
        BaseRepresentation::from_base("Capacitance"),
        1.0,
        Unit::from_base_unit("C").div(&Unit::from_base_unit("V")),
    );
    add_derived_alias(&mut reg, "farad", "Capacitance", Unit::from_base_unit("F"));

    // Resistance: ohm = V/A (symbol Ω not in Ident, use "ohm")
    reg.dimensions.add_base_dimension("Resistance");
    reg.add_derived_unit(
        "ohm",
        BaseRepresentation::from_base("Resistance"),
        1.0,
        Unit::from_base_unit("V").div(&Unit::from_base_unit("A")),
    );

    // Conductance: S = A/V (siemens)
    reg.dimensions.add_base_dimension("Conductance");
    reg.add_derived_unit(
        "S",
        BaseRepresentation::from_base("Conductance"),
        1.0,
        Unit::from_base_unit("A").div(&Unit::from_base_unit("V")),
    );
    add_derived_alias(&mut reg, "siemens", "Conductance", Unit::from_base_unit("S"));

    // Magnetic flux: Wb = V·s
    reg.dimensions.add_base_dimension("MagneticFlux");
    reg.add_derived_unit(
        "Wb",
        BaseRepresentation::from_base("MagneticFlux"),
        1.0,
        Unit::from_base_unit("V").mul(&Unit::from_base_unit("s")),
    );
    add_derived_alias(&mut reg, "weber", "MagneticFlux", Unit::from_base_unit("Wb"));

    // Magnetic flux density: T = Wb/m²
    reg.dimensions.add_base_dimension("MagneticFluxDensity");
    reg.add_derived_unit(
        "T",
        BaseRepresentation::from_base("MagneticFluxDensity"),
        1.0,
        Unit::from_base_unit("Wb").div(&Unit::from_base_unit("m").powi(2)),
    );
    add_derived_alias(&mut reg, "tesla", "MagneticFluxDensity", Unit::from_base_unit("T"));

    // Inductance: H = Wb/A
    reg.dimensions.add_base_dimension("Inductance");
    reg.add_derived_unit(
        "H",
        BaseRepresentation::from_base("Inductance"),
        1.0,
        Unit::from_base_unit("Wb").div(&Unit::from_base_unit("A")),
    );
    add_derived_alias(&mut reg, "henry", "Inductance", Unit::from_base_unit("H"));

    // Luminous flux: lm = cd (steradian is dimensionless)
    reg.dimensions.add_base_dimension("LuminousFlux");
    reg.add_derived_unit(
        "lm",
        BaseRepresentation::from_base("LuminousFlux"),
        1.0,
        Unit::from_base_unit("cd"),
    );
    add_derived_alias(&mut reg, "lumen", "LuminousFlux", Unit::from_base_unit("lm"));

    // Illuminance: lx = lm/m²
    reg.dimensions.add_base_dimension("Illuminance");
    reg.add_derived_unit(
        "lx",
        BaseRepresentation::from_base("Illuminance"),
        1.0,
        Unit::from_base_unit("lm").div(&Unit::from_base_unit("m").powi(2)),
    );
    add_derived_alias(&mut reg, "lux", "Illuminance", Unit::from_base_unit("lx"));

    // Activity (radioactivity): Bq = s⁻¹
    reg.dimensions.add_base_dimension("Activity");
    reg.add_derived_unit(
        "Bq",
        BaseRepresentation::from_base("Activity"),
        1.0,
        Unit::from_base_unit("s").powi(-1),
    );
    add_derived_alias(&mut reg, "becquerel", "Activity", Unit::from_base_unit("Bq"));

    // Absorbed dose: Gy = J/kg
    reg.dimensions.add_base_dimension("AbsorbedDose");
    reg.add_derived_unit(
        "Gy",
        BaseRepresentation::from_base("AbsorbedDose"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("kg")),
    );
    add_derived_alias(&mut reg, "gray", "AbsorbedDose", Unit::from_base_unit("Gy"));

    // Equivalent dose: Sv = J/kg (same dimension as Gy, different quantity type)
    reg.dimensions.add_base_dimension("EquivalentDose");
    reg.add_derived_unit(
        "Sv",
        BaseRepresentation::from_base("EquivalentDose"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("kg")),
    );
    add_derived_alias(&mut reg, "sievert", "EquivalentDose", Unit::from_base_unit("Sv"));

    // Catalytic activity: kat = mol/s
    reg.dimensions.add_base_dimension("CatalyticActivity");
    reg.add_derived_unit(
        "kat",
        BaseRepresentation::from_base("CatalyticActivity"),
        1.0,
        Unit::from_base_unit("mol").div(&Unit::from_base_unit("s")),
    );
    add_derived_alias(&mut reg, "katal", "CatalyticActivity", Unit::from_base_unit("kat"));

    // Degree Celsius: same dimension as K, factor 1 (offset 273.15 not modeled)
    add_derived_alias(&mut reg, "celsius", "Temperature", Unit::from_base_unit("K"));
    // Fahrenheit: scale factor 5/9 for temperature differences (absolute zero-point 32°F = 0°C not modeled)
    reg.add_derived_unit(
        "fahrenheit",
        BaseRepresentation::from_base("Temperature"),
        5.0 / 9.0,
        Unit::from_base_unit("K"),
    );

    // Concentration: molar = 1 mol/L (AmountOfSubstance/Volume)
    reg.dimensions.add_base_dimension("Concentration");
    let mol_per_liter = Unit::from_base_unit("mol").div(&Unit::from_base_unit("liter"));
    reg.add_derived_unit(
        "molar",
        BaseRepresentation::from_base("Concentration"),
        1.0,
        mol_per_liter,
    );
    add_derived_alias(&mut reg, "M", "Concentration", Unit::from_base_unit("molar"));

    // Dimensionless ratios: percent = 0.01, ppm = 1e-6, ppb = 1e-9 (note: % is the modulo operator, use "percent")
    reg.add_derived_unit(
        "percent",
        BaseRepresentation::unity(),
        0.01,
        Unit::scalar(),
    );
    reg.add_derived_unit(
        "ppm",
        BaseRepresentation::unity(),
        1e-6,
        Unit::scalar(),
    );
    reg.add_derived_unit(
        "ppb",
        BaseRepresentation::unity(),
        1e-9,
        Unit::scalar(),
    );

    // Solid angle: steradian (sr) — dimensionless in SI, factor 1
    reg.add_derived_unit(
        "steradian",
        BaseRepresentation::unity(),
        1.0,
        Unit::scalar(),
    );
    reg.add_derived_unit(
        "sr",
        BaseRepresentation::unity(),
        1.0,
        Unit::scalar(),
    );

    reg
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::quantity::Quantity;

    #[test]
    fn to_base_base_unit() {
        let reg = default_si_registry();
        let m = Unit::from_base_unit("m");
        let (u, f) = reg.to_base_unit_representation(&m).unwrap();
        assert!((f - 1.0).abs() < 1e-10);
        assert_eq!(u.iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn to_base_derived() {
        let reg = default_si_registry();
        let hour = Unit::from_base_unit("hour");
        let (u, f) = reg.to_base_unit_representation(&hour).unwrap();
        assert!((f - 3600.0).abs() < 1e-10);
        assert_eq!(u.iter().next().unwrap().unit_name, "s");
    }

    #[test]
    fn same_dimension() {
        let reg = default_si_registry();
        let m = Unit::from_base_unit("m");
        let km = Unit::from_base_unit("km");
        assert!(reg.same_dimension(&m, &km).unwrap());
        let s = Unit::from_base_unit("s");
        assert!(!reg.same_dimension(&m, &s).unwrap());
    }

    #[test]
    fn degrees_unit_is_registered() {
        let reg = default_si_registry();
        assert!(
            reg.get_unit_with_prefix("degrees").is_some(),
            "\"degrees\" must resolve as a unit so that 180 * degrees = 180 degree"
        );
    }

    /// 180 degree (singular) converts to π rad; same_dimension(rad, degree).
    #[test]
    fn angle_rad_degree_same_dimension_and_convert() {
        let reg = default_si_registry();
        let rad = Unit::from_base_unit("rad");
        let degree = Unit::from_base_unit("degree");
        assert!(reg.same_dimension(&rad, &degree).unwrap());
        let q_180_deg = Quantity::new(180.0, degree);
        let as_rad = q_180_deg.convert_to(&reg, &rad).unwrap();
        assert!((as_rad.value() - std::f64::consts::PI).abs() < 1e-10, "180 degree = π rad");
    }

    /// Regression: "degrees" is a derived alias of "degree"; 180 degrees must convert to π rad
    /// (to_base_unit_representation must include defining unit's factor for aliases).
    #[test]
    fn degrees_alias_converts_180_to_pi_rad() {
        let reg = default_si_registry();
        let degrees = reg.get_unit_with_prefix("degrees").unwrap();
        let rad = Unit::from_base_unit("rad");
        let q_180 = Quantity::new(180.0, degrees);
        let as_rad = q_180.convert_to(&reg, &rad).unwrap();
        assert!(
            (as_rad.value() - std::f64::consts::PI).abs() < 1e-10,
            "180 degrees = π rad (got {}); alias conversion must use degree factor",
            as_rad.value()
        );
    }

    #[test]
    fn get_unit_with_prefix_km() {
        let reg = default_si_registry();
        let u = reg.get_unit_with_prefix("km").unwrap();
        let (base, factor) = reg.to_base_unit_representation(&u).unwrap();
        assert_eq!(base.iter().next().unwrap().unit_name, "m");
        assert!((factor - 1000.0).abs() < 1e-10);
    }

    #[test]
    fn get_unit_with_prefix_mm() {
        let reg = default_si_registry();
        let u = reg.get_unit_with_prefix("mm").unwrap();
        let (base, factor) = reg.to_base_unit_representation(&u).unwrap();
        assert_eq!(base.iter().next().unwrap().unit_name, "m");
        assert!((factor - 0.001).abs() < 1e-10);
    }

    // --- Area dimension and units ---

    #[test]
    fn area_same_dimension_m2_and_m_times_m() {
        let reg = default_si_registry();
        let m2 = Unit::from_base_unit("m2");
        let m_times_m = Unit::from_base_unit("m").powi(2);
        assert!(reg.same_dimension(&m2, &m_times_m).unwrap());
    }

    #[test]
    fn area_are_equals_100_m2() {
        let reg = default_si_registry();
        let are = Unit::from_base_unit("are");
        let m2 = Unit::from_base_unit("m2");
        let q_are = Quantity::new(1.0, are);
        let as_m2 = q_are.convert_to(&reg, &m2).unwrap();
        assert!((as_m2.value() - 100.0).abs() < 1e-10, "1 are = 100 m²");
    }

    #[test]
    fn area_hectare_equals_10000_m2() {
        let reg = default_si_registry();
        let hectare = reg.get_unit_with_prefix("hectare").unwrap();
        let m2 = Unit::from_base_unit("m2");
        let q_ha = Quantity::new(1.0, hectare);
        let as_m2 = q_ha.convert_to(&reg, &m2).unwrap();
        assert!((as_m2.value() - 10_000.0).abs() < 1e-10, "1 hectare = 10 000 m²");
    }

    #[test]
    fn area_ha_alias_equals_10000_m2() {
        let reg = default_si_registry();
        let ha = reg.get_unit_with_prefix("ha").unwrap();
        let m2 = Unit::from_base_unit("m2");
        let q = Quantity::new(1.0, ha);
        let as_m2 = q.convert_to(&reg, &m2).unwrap();
        assert!((as_m2.value() - 10_000.0).abs() < 1e-10, "1 ha = 10 000 m²");
    }

    #[test]
    fn area_km2_as_m2_is_1e6() {
        let q = crate::run_numeric("1 km2 as m2").unwrap();
        assert!((q.value() - 1e6).abs() < 1.0, "1 km² = 10⁶ m²");
    }

    #[test]
    fn area_m2_as_km2_is_1e_minus_6() {
        let q = crate::run_numeric("1 m2 as km2").unwrap();
        assert!((q.value() - 1e-6).abs() < 1e-15, "1 m² = 10⁻⁶ km²");
    }

    #[test]
    fn area_cm2_as_m2_is_1e_minus_4() {
        let q = crate::run_numeric("1 cm2 as m2").unwrap();
        assert!((q.value() - 1e-4).abs() < 1e-12, "1 cm² = 10⁻⁴ m²");
    }

    #[test]
    fn area_mm2_as_m2_is_1e_minus_6() {
        let q = crate::run_numeric("1 mm2 as m2").unwrap();
        assert!((q.value() - 1e-6).abs() < 1e-15, "1 mm² = 10⁻⁶ m²");
    }

    #[test]
    fn area_km_times_km_same_dimension_as_m2_and_converts() {
        let reg = default_si_registry();
        let q = crate::run_numeric("1 km * 1 km").unwrap();
        let m2 = Unit::from_base_unit("m2");
        assert!(reg.same_dimension(q.unit(), &m2).unwrap());
        let as_m2 = q.convert_to(&reg, &m2).unwrap();
        assert!((as_m2.value() - 1e6).abs() < 1.0, "1 km × 1 km = 10⁶ m²");
    }

    #[test]
    fn area_parsing_m2_squaremeter_squareinch_ha_hectare_are() {
        let cases = [
            "1 m2", "1 squaremeter", "1 squareinch", "1 ha", "1 hectare", "1 are", "1 in2", "1 sqin",
            "1 sqft", "1 squarefoot", "1 ft2", "1 foot", "1 ft",
        ];
        for expr in cases {
            let q = crate::run_numeric(expr).unwrap_or_else(|e| panic!("{expr}: {e}"));
            assert!((q.value() - 1.0).abs() < 1e-12, "{}", expr);
        }
    }

    // --- STEM units and constants: volume, pressure, mass, temperature, energy, power,
    //     concentration, percent/ppm/ppb, angles, knot/nmi, steradian ---

    // --- Volume dimension and units ---

    #[test]
    fn volume_same_dimension_m3_and_m_cubed() {
        let reg = default_si_registry();
        let m3 = Unit::from_base_unit("m3");
        let m_cubed = Unit::from_base_unit("m").powi(3);
        assert!(reg.same_dimension(&m3, &m_cubed).unwrap());
    }

    #[test]
    fn volume_liter_equals_0_001_m3() {
        let reg = default_si_registry();
        let liter = Unit::from_base_unit("liter");
        let m3 = Unit::from_base_unit("m3");
        let q_l = Quantity::new(1.0, liter);
        let as_m3 = q_l.convert_to(&reg, &m3).unwrap();
        assert!((as_m3.value() - 0.001).abs() < 1e-10, "1 L = 10⁻³ m³");
    }

    #[test]
    fn volume_km3_as_m3_is_1e9() {
        let q = crate::run_numeric("1 km3 as m3").unwrap();
        assert!((q.value() - 1e9).abs() < 1.0, "1 km³ = 10⁹ m³");
    }

    #[test]
    fn volume_parsing_m3_liter_ml() {
        let cases = [
            "1 m3", "1 m³", "1 cubicmeter", "1 liter", "1 litre", "1 L", "1 milliliter", "1 ml", "1 mL",
        ];
        for expr in cases {
            let q = crate::run_numeric(expr).unwrap_or_else(|e| panic!("{expr}: {e}"));
            assert!((q.value() - 1.0).abs() < 1e-12, "{}", expr);
        }
    }

    /// Cubed-length prefix resolution: 1 cm³ and 1 mm³ convert correctly to m³.
    #[test]
    fn volume_cm3_mm3_prefix_resolution() {
        let q_cm3 = crate::run_numeric("1 cm3 as m3").unwrap();
        assert!((q_cm3.value() - 1e-6).abs() < 1e-12, "1 cm³ = 10⁻⁶ m³");
        let q_mm3 = crate::run_numeric("1 mm3 as m3").unwrap();
        assert!((q_mm3.value() - 1e-9).abs() < 1e-15, "1 mm³ = 10⁻⁹ m³");
    }

    // --- Phase 2: pressure, mass, temperature F, energy, power ---

    #[test]
    fn stem_pressure_units_convert() {
        let q_bar = crate::run_numeric("1 bar as Pa").unwrap();
        assert!((q_bar.value() - 100_000.0).abs() < 1.0, "1 bar = 10⁵ Pa");
        let q_atm = crate::run_numeric("1 atm as Pa").unwrap();
        assert!((q_atm.value() - 101_325.0).abs() < 1.0, "1 atm ≈ 101325 Pa");
        let q_psi = crate::run_numeric("1 psi as Pa").unwrap();
        assert!((q_psi.value() - 6894.757).abs() < 0.01, "1 psi ≈ 6894.76 Pa");
        let q_mmhg = crate::run_numeric("1 mmHg as Pa").unwrap();
        assert!((q_mmhg.value() - 133.322).abs() < 0.001, "1 mmHg ≈ 133.32 Pa");
        let q_torr = crate::run_numeric("1 torr as mmHg").unwrap();
        assert!((q_torr.value() - 1.0).abs() < 1e-10, "1 torr = 1 mmHg");
    }

    #[test]
    fn stem_pound_and_ounce_convert() {
        let q = crate::run_numeric("1 pound as kg").unwrap();
        assert!((q.value() - 0.45359237).abs() < 1e-8, "1 lb = 0.45359237 kg");
        let q_oz = crate::run_numeric("16 ounce as pound").unwrap();
        assert!((q_oz.value() - 1.0).abs() < 1e-10, "16 oz = 1 lb");
    }

    #[test]
    fn stem_fahrenheit_scale_factor() {
        // Temperature difference: 9 fahrenheit = 5 K (so 1 fahrenheit = 5/9 K)
        let q = crate::run_numeric("9 fahrenheit as K").unwrap();
        assert!((q.value() - 5.0).abs() < 1e-10, "9 °F difference = 5 K difference");
    }

    #[test]
    fn stem_calorie_and_btu_convert() {
        let q = crate::run_numeric("1 calorie as joule").unwrap();
        assert!((q.value() - 4.184).abs() < 1e-10, "1 cal = 4.184 J");
        let q_wh = crate::run_numeric("1 Wh as joule").unwrap();
        assert!((q_wh.value() - 3600.0).abs() < 1e-6, "1 Wh = 3600 J");
        let q_kcal = crate::run_numeric("1 kcal as joule").unwrap();
        assert!((q_kcal.value() - 4184.0).abs() < 1e-6, "1 kcal = 4184 J");
        let q_btu = crate::run_numeric("1 BTU as joule").unwrap();
        assert!((q_btu.value() - 1055.06).abs() < 0.1, "1 BTU ≈ 1055 J");
        let q_kwh = crate::run_numeric("1 kWh as joule").unwrap();
        assert!((q_kwh.value() - 3_600_000.0).abs() < 1.0, "1 kWh = 3.6e6 J");
    }

    #[test]
    fn stem_horsepower_convert() {
        let q = crate::run_numeric("1 hp as W").unwrap();
        assert!((q.value() - 745.7).abs() < 0.1, "1 hp ≈ 745.7 W");
    }

    // --- Phase 3: concentration, percent, ppm, ppb ---

    #[test]
    fn stem_molar_parses_and_same_dimension_as_mol_per_liter() {
        let reg = default_si_registry();
        let molar = Unit::from_base_unit("molar");
        let mol_per_l = Unit::from_base_unit("mol").div(&Unit::from_base_unit("liter"));
        assert!(reg.same_dimension(&molar, &mol_per_l).unwrap(), "molar = mol/L");
        let q = crate::run_numeric("1 molar").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-12);
    }

    /// Molar alias "M" parses and has same dimension as molar (mol/L).
    #[test]
    fn stem_molar_m_alias_parses_and_equals_molar() {
        let reg = default_si_registry();
        let q_m = crate::run_numeric("1 M").unwrap();
        assert!((q_m.value() - 1.0).abs() < 1e-12, "1 M = 1 molar");
        assert!(reg.same_dimension(q_m.unit(), &Unit::from_base_unit("molar")).unwrap());
    }

    #[test]
    fn stem_percent_ppm_ppb_dimensionless() {
        let reg = default_si_registry();
        let scalar = Unit::scalar();
        let q_100_percent = Quantity::new(100.0, Unit::from_base_unit("percent"));
        let as_scalar = q_100_percent.convert_to(&reg, &scalar).unwrap();
        assert!((as_scalar.value() - 1.0).abs() < 1e-10, "100 percent = 1 (scalar)");
        let q_1_ppm = Quantity::new(1.0, Unit::from_base_unit("ppm"));
        let as_s = q_1_ppm.convert_to(&reg, &scalar).unwrap();
        assert!((as_s.value() - 1e-6).abs() < 1e-15, "1 ppm = 1e-6 (scalar)");
        let q_1_ppb = Quantity::new(1.0, Unit::from_base_unit("ppb"));
        let as_s_ppb = q_1_ppb.convert_to(&reg, &scalar).unwrap();
        assert!((as_s_ppb.value() - 1e-9).abs() < 1e-18, "1 ppb = 1e-9 (scalar)");
    }

    /// run_numeric parses percent/ppm/ppb and conversion to scalar yields correct factor.
    #[test]
    fn stem_percent_ppm_ppb_run_numeric() {
        let reg = default_si_registry();
        let scalar = Unit::scalar();
        let q_100 = crate::run_numeric("100 percent").unwrap();
        assert!((q_100.value() - 100.0).abs() < 1e-10);
        let as_one = q_100.convert_to(&reg, &scalar).unwrap();
        assert!((as_one.value() - 1.0).abs() < 1e-10, "100 percent as scalar = 1");
        let q_50 = crate::run_numeric("50 percent").unwrap();
        let as_half = q_50.convert_to(&reg, &scalar).unwrap();
        assert!((as_half.value() - 0.5).abs() < 1e-10, "50 percent as scalar = 0.5");
        let q_ppm = crate::run_numeric("1 ppm").unwrap();
        assert!((q_ppm.value() - 1.0).abs() < 1e-12);
        let q_ppb = crate::run_numeric("1 ppb").unwrap();
        assert!((q_ppb.value() - 1.0).abs() < 1e-12);
    }

    // --- Phase 4: arcmin, arcsec, knot, steradian ---

    #[test]
    fn stem_arcmin_arcsec_convert() {
        let reg = default_si_registry();
        let degree = Unit::from_base_unit("degree");
        let q_60_arcmin = Quantity::new(60.0, Unit::from_base_unit("arcmin"));
        let as_deg = q_60_arcmin.convert_to(&reg, &degree).unwrap();
        assert!((as_deg.value() - 1.0).abs() < 1e-10, "60 arcmin = 1 degree");
        let q_3600_arcsec = Quantity::new(3600.0, Unit::from_base_unit("arcsec"));
        let as_deg_sec = q_3600_arcsec.convert_to(&reg, &degree).unwrap();
        assert!((as_deg_sec.value() - 1.0).abs() < 1e-10, "3600 arcsec = 1 degree");
    }

    #[test]
    fn stem_knot_convert_to_m_per_s() {
        let q = crate::run_numeric("1 knot as m / s").unwrap();
        let expected = 1852.0 / 3600.0;
        assert!((q.value() - expected).abs() < 1e-6, "1 knot = {} m/s", expected);
    }

    /// Nautical mile and nmi alias convert to 1852 m.
    #[test]
    fn stem_nautical_mile_convert() {
        let q = crate::run_numeric("1 nautical_mile as m").unwrap();
        assert!((q.value() - 1852.0).abs() < 1e-6, "1 nmi = 1852 m");
        let q_nmi = crate::run_numeric("1 nmi as m").unwrap();
        assert!((q_nmi.value() - 1852.0).abs() < 1e-6, "1 nmi alias = 1852 m");
    }

    #[test]
    fn stem_steradian_dimensionless() {
        let reg = default_si_registry();
        let q = Quantity::new(1.0, Unit::from_base_unit("steradian"));
        let scalar = Unit::scalar();
        let as_s = q.convert_to(&reg, &scalar).unwrap();
        assert!((as_s.value() - 1.0).abs() < 1e-12, "1 sr = 1 (scalar)");
    }

    /// Steradian alias "sr" parses via run_numeric and converts to scalar (complements stem_steradian_dimensionless).
    #[test]
    fn stem_sr_alias_parses() {
        let q = crate::run_numeric("1 sr").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-12, "1 sr parses");
        let reg = default_si_registry();
        let as_scalar = q.convert_to(&reg, &Unit::scalar()).unwrap();
        assert!((as_scalar.value() - 1.0).abs() < 1e-12);
    }
}

/// Extensive tests for SI base units, derived units, prefixes, and compound expressions.
#[cfg(test)]
mod si_tests {
    use super::*;
    use crate::quantity::Quantity;
    use crate::unit::Unit;

    /// All 7 SI base units (BIPM): metre, kilogram, second, ampere, kelvin, mole, candela.
    const SI_BASE_UNITS: &[&str] = &["m", "kg", "s", "A", "K", "mol", "cd"];

    #[test]
    fn si_base_units_all_parse_and_evaluate() {
        let reg = default_si_registry();
        for name in SI_BASE_UNITS {
            let u = reg.get_unit_with_prefix(name).expect(name);
            let (base, factor) = reg.to_base_unit_representation(&u).unwrap();
            assert_eq!(base.iter().count(), 1, "base unit {name} should expand to one factor");
            assert_eq!(base.iter().next().unwrap().unit_name, *name);
            assert!((factor - 1.0).abs() < 1e-12, "base unit {name} factor should be 1");
        }
    }

    #[test]
    fn si_base_units_run_as_quantity_literal() {
        for name in SI_BASE_UNITS {
            let expr = format!("1 {name}");
            let q = crate::run_numeric(&expr).unwrap_or_else(|e| panic!("run_numeric({expr:?}): {e}"));
            assert!((q.value() - 1.0).abs() < 1e-12, "{}", expr);
            assert_eq!(q.unit().iter().next().unwrap().unit_name, *name);
        }
    }

    /// Key SI derived units we register (symbol or name, approximate factor to base, base unit to expect in expansion).
    const SI_DERIVED_UNITS: &[(&str, f64, &str)] = &[
        ("km", 1000.0, "m"),
        ("g", 0.001, "kg"),
        ("hour", 3600.0, "s"),
        ("minute", 60.0, "s"),
        // day = 24 h, week = 7 d, year = 365.25 d (Julian); month = year/12, quarter = year/4
        ("day", 86400.0, "s"),
        ("week", 604_800.0, "s"),
        ("year", 31_557_600.0, "s"),
        ("month", 2_629_800.0, "s"),
        ("quarter", 7_889_400.0, "s"),
        ("decade", 315_576_000.0, "s"),
        ("century", 3_155_760_000.0, "s"),
        ("millennium", 31_557_600_000.0, "s"),
        ("Hz", 1.0, "s"),
        ("joule", 1.0, "kg"),
        ("J", 1.0, "kg"),
        ("N", 1.0, "kg"),
        ("Pa", 1.0, "kg"),
        ("W", 1.0, "kg"),
        ("C", 1.0, "A"),
        ("V", 1.0, "kg"),
        ("ohm", 1.0, "kg"),
        ("Bq", 1.0, "s"),
        ("lm", 1.0, "cd"),
        ("Gy", 1.0, "m"),   // J/kg → m²·s⁻²
        ("kat", 1.0, "mol"),
    ];

    #[test]
    fn si_derived_units_resolve_and_convert_to_base() {
        let reg = default_si_registry();
        for (name, expected_factor, base_contains) in SI_DERIVED_UNITS {
            let u = reg.get_unit_with_prefix(name).expect(name);
            let (base_u, factor) = reg.to_base_unit_representation(&u).unwrap();
            assert!(
                base_u.iter().any(|f| f.unit_name.as_str() == *base_contains),
                "derived {name} should expand to contain {base_contains}"
            );
            if *name == "Hz" {
                assert!((factor - 1.0).abs() < 1e-12, "Hz factor");
            } else if *name != "Hz" {
                assert!(
                    (factor - expected_factor).abs() < 1e-6 * expected_factor.max(1.0),
                    "derived {name} factor"
                );
            }
        }
    }

    #[test]
    fn time_units_convert_correctly() {
        const SECONDS_PER_DAY: f64 = 24.0 * 3600.0; // match day = 24 hour, hour = 3600 s
        let reg = default_si_registry();
        // 10 hours as day = 10/24 days
        let q = crate::run_numeric_with_registry(
            "10 hours as day",
            &reg,
            &crate::SymbolRegistry::default_registry(),
        )
        .unwrap();
        assert!((q.value() - 10.0 / 24.0).abs() < 1e-10, "10 hours as day");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "day");
        // Plural "days" and "weeks" resolve via singularize
        let q_days = crate::run_numeric("2 days").unwrap();
        assert!((q_days.value() - 2.0).abs() < 1e-12);
        assert_eq!(q_days.unit().iter().next().unwrap().unit_name, "day");
        let q_weeks = crate::run_numeric("1 weeks").unwrap();
        assert!((q_weeks.value() - 1.0).abs() < 1e-12);
        assert_eq!(q_weeks.unit().iter().next().unwrap().unit_name, "week");
        // 1 day -> seconds in base representation
        let day = Unit::from_base_unit("day");
        let (base_u, factor) = reg.to_base_unit_representation(&day).unwrap();
        assert_eq!(base_u.iter().next().unwrap().unit_name, "s");
        assert!(
            (factor - SECONDS_PER_DAY).abs() < 1e-6 * SECONDS_PER_DAY,
            "1 day = {} s",
            SECONDS_PER_DAY
        );
        // 1 week = 7 days
        let week = Unit::from_base_unit("week");
        let (_, week_factor) = reg.to_base_unit_representation(&week).unwrap();
        assert!(
            (week_factor - 7.0 * SECONDS_PER_DAY).abs() < 1e-6 * (7.0 * SECONDS_PER_DAY),
            "1 week = 7 * {} s",
            SECONDS_PER_DAY
        );
    }

    #[test]
    fn si_metric_prefixes_on_length() {
        let reg = default_si_registry();
        let cases = [
            ("mm", 0.001),
            ("cm", 0.01),
            ("dm", 0.1),
            ("m", 1.0),
            ("dam", 10.0),
            ("hm", 100.0),
            ("km", 1000.0),
            ("Mm", 1e6),
            ("µm", 1e-6),
            ("nm", 1e-9),
        ];
        for (ident, expected_factor) in cases {
            let u = reg.get_unit_with_prefix(ident).unwrap_or_else(|| {
                panic!("prefix unit {ident} should resolve")
            });
            let (_, factor) = reg.to_base_unit_representation(&u).unwrap();
            assert!(
                (factor - expected_factor).abs() < 1e-10 * expected_factor.max(1e-15),
                "{}",
                ident
            );
        }
    }

    #[test]
    fn si_metric_prefixes_on_mass() {
        let reg = default_si_registry();
        assert!(reg.get_unit_with_prefix("kg").is_some());
        let u = reg.get_unit_with_prefix("mg").expect("mg");
        let (_, factor) = reg.to_base_unit_representation(&u).unwrap();
        assert!((factor - 0.000_001).abs() < 1e-12);
    }

    #[test]
    fn si_same_dimension_length_units() {
        let reg = default_si_registry();
        let length_units = ["m", "km", "mm", "mile", "au"];
        for a in length_units {
            for b in length_units {
                let ua = reg.get_unit_with_prefix(a).unwrap();
                let ub = reg.get_unit_with_prefix(b).unwrap();
                assert!(reg.same_dimension(&ua, &ub).unwrap(), "{a} vs {b}");
            }
        }
    }

    #[test]
    fn si_same_dimension_time_units() {
        let reg = default_si_registry();
        let time_units = [
            "s", "second", "minute", "hour", "day", "week", "month", "quarter",
            "year", "decade", "century", "millennium",
        ];
        for a in time_units {
            for b in time_units {
                let ua = reg.get_unit_with_prefix(a).unwrap();
                let ub = reg.get_unit_with_prefix(b).unwrap();
                assert!(reg.same_dimension(&ua, &ub).unwrap(), "{a} vs {b}");
            }
        }
    }

    #[test]
    fn si_add_length_conversion() {
        let q = crate::run_numeric("1 km + 500 m").unwrap();
        assert!((q.value() - 1500.0).abs() < 1e-6, "1 km + 500 m = 1500 m");
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn si_compound_velocity_m_per_s() {
        let q = crate::run_numeric("10 m / 2 s").unwrap();
        assert!((q.value() - 5.0).abs() < 1e-10);
        let factors: Vec<_> = q.unit().iter().map(|f| f.unit_name.as_str()).collect();
        assert!(factors.contains(&"m"));
        assert!(factors.contains(&"s"));
    }

    #[test]
    fn si_compound_force_newton() {
        let reg = default_si_registry();
        let q = crate::run_numeric("1 kg * 1 m / 1 s / 1 s").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10);
        let n = Unit::from_base_unit("N");
        assert!(reg.same_dimension(q.unit(), &n).unwrap());
    }

    #[test]
    fn si_compound_power_watt() {
        let reg = default_si_registry();
        let q = crate::run_numeric("1 joule / 1 s").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10);
        let w = Unit::from_base_unit("W");
        assert!(reg.same_dimension(q.unit(), &w).unwrap());
    }

    #[test]
    fn si_compound_energy_joule() {
        let reg = default_si_registry();
        let q = crate::run_numeric("1 N * 1 m").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-10);
        let j = Unit::from_base_unit("joule");
        assert!(reg.same_dimension(q.unit(), &j).unwrap());
    }

    #[test]
    fn si_frequency_hertz() {
        let q = crate::run_numeric("1 Hz").unwrap();
        assert!((q.value() - 1.0).abs() < 1e-12);
        assert_eq!(q.unit().iter().next().unwrap().unit_name, "Hz");
    }

    #[test]
    fn si_convert_gram_to_kg() {
        let reg = default_si_registry();
        let q = Quantity::new(1000.0, Unit::from_base_unit("g"));
        let kg = Unit::from_base_unit("kg");
        let c = q.convert_to(&reg, &kg).unwrap();
        assert!((c.value() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn si_convert_hour_to_seconds() {
        let reg = default_si_registry();
        let q = Quantity::new(1.0, Unit::from_base_unit("hour"));
        let s = Unit::from_base_unit("s");
        let c = q.convert_to(&reg, &s).unwrap();
        assert!((c.value() - 3600.0).abs() < 1e-6);
    }
}

/// Tests that every registered unit parses and evaluates, and documents Numbat units we do not support.
#[cfg(test)]
mod all_units_tests {
    use super::*;

    /// Every unit in the default registry must parse as "1 <name>" and evaluate to quantity 1 in that unit.
    #[test]
    fn every_registered_unit_parses_and_evaluates() {
        let reg = default_si_registry();
        let names: Vec<String> = reg.unit_names().cloned().collect();
        assert!(!names.is_empty(), "registry has at least one unit");
        for name in &names {
            let expr = format!("1 {name}");
            let q = crate::run_numeric(&expr).unwrap_or_else(|e| panic!("run_numeric({expr:?}) failed: {e}"));
            assert!((q.value() - 1.0).abs() < 1e-12, "{}", expr);
            assert_eq!(q.unit().iter().next().unwrap().unit_name, *name, "{}", expr);
        }
    }

    /// Run "1 <name>" for each name; used to get a fixed list for documentation.
    #[test]
    fn registered_units_list() {
        let reg = default_si_registry();
        let names: Vec<String> = reg.unit_names().cloned().collect();
        let mut sorted = names.clone();
        sorted.sort();
        for name in &sorted {
            let q = crate::run_numeric(&format!("1 {name}")).unwrap();
            assert!((q.value() - 1.0).abs() < 1e-12);
        }
    }

    /// Numbat supports many more units (e.g. pound). We treat unknown identifiers
    /// as symbols, so run() succeeds with Value::Symbolic; run_numeric() fails with SymbolHasNoValue.
    #[test]
    fn numbat_units_we_do_not_support_treated_as_symbols() {
        use crate::Value;
        let unsupported = ["stone"];
        for name in unsupported {
            let expr = format!("1 {name}");
            let res = crate::run(&expr);
            assert!(res.is_ok(), "run({expr}) should succeed (symbolic)");
            let v = res.unwrap();
            assert!(matches!(v, Value::Symbolic(_)), "{} should be symbolic", expr);
            assert!(crate::run_numeric(&expr).is_err(), "run_numeric({expr}) should fail (no value for symbol)");
        }
    }
}
