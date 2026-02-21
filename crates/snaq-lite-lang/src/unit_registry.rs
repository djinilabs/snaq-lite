//! Unit registry: base and derived units, resolution to base representation.
//! Supports prefix parsing (e.g. "km" → kilo × meter).

use crate::dimension::{BaseRepresentation, DimensionRegistry};
use crate::prefix::{self, Prefix};
use crate::unit::{Unit, UnitFactor};
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

    /// Resolve identifier to Unit: exact name first, then prefix + base unit (e.g. "km" → kilo×m).
    /// Prefixes tried longest-first so "Mm" → mega×m not milli×"m" (invalid).
    pub fn get_unit_with_prefix(&self, ident: &str) -> Option<Unit> {
        if self.units.contains_key(ident) {
            return self.get_unit(ident);
        }
        let prefixes = prefix::metric_short_prefixes();
        let mut by_len: Vec<_> = prefixes.iter().collect();
        by_len.sort_by_key(|(s, _)| std::cmp::Reverse(s.len()));
        for (symbol, p) in by_len {
            if ident.len() > symbol.len() && ident.starts_with(symbol) {
                let base = &ident[symbol.len()..];
                if self.units.contains_key(base) {
                    let u = self.get_unit(base).unwrap();
                    return Some(u.with_prefix(*p));
                }
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
                    let (base_u, _def_base_factor) =
                        self.to_base_unit_representation(defining_unit)?;
                    result_unit = result_unit.mul(&base_u.power(f.exponent));
                    result_factor *= (prefix_factor * factor).powf(exp_f64);
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
/// **SI derived (with special names):** J, C, V, F, ohm, S, Wb, T, H, Hz, N, Pa, W, lm, lx, Bq, Gy, Sv, kat; km, g, hour, minute, second, seconds; plus mile, au, parsec, light_year, eV, celsius.
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
    add_derived_alias(&mut reg, "amperes", "Current", Unit::from_base_unit("A"));
    add_derived_alias(&mut reg, "kelvin", "Temperature", Unit::from_base_unit("K"));
    add_derived_alias(&mut reg, "kelvins", "Temperature", Unit::from_base_unit("K"));
    add_derived_alias(&mut reg, "mole", "AmountOfSubstance", Unit::from_base_unit("mol"));
    add_derived_alias(&mut reg, "moles", "AmountOfSubstance", Unit::from_base_unit("mol"));
    add_derived_alias(&mut reg, "candela", "LuminousIntensity", Unit::from_base_unit("cd"));
    add_derived_alias(&mut reg, "candelas", "LuminousIntensity", Unit::from_base_unit("cd"));

    // Angle: rad (base), degree = π/180 rad
    reg.add_derived_unit(
        "degree",
        BaseRepresentation::from_base("Angle"),
        std::f64::consts::PI / 180.0,
        Unit::from_base_unit("rad"),
    );
    add_derived_alias(&mut reg, "degrees", "Angle", Unit::from_base_unit("degree"));

    // Length: SI derived + Numbat parity (with long-form aliases)
    reg.add_derived_unit(
        "meter",
        BaseRepresentation::from_base("Length"),
        1.0,
        Unit::from_base_unit("m"),
    );
    reg.add_derived_unit(
        "meters",
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
        "kilometers",
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

    // Time: SI derived
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
        "seconds",
        BaseRepresentation::from_base("Time"),
        1.0,
        Unit::from_base_unit("s"),
    );
    reg.dimensions.add_base_dimension("Frequency");
    reg.add_derived_unit(
        "Hz",
        BaseRepresentation::from_base("Frequency"),
        1.0,
        Unit::from_base_unit("s").powi(-1),
    );

    // Mass: SI derived (gram)
    reg.add_derived_unit(
        "g",
        BaseRepresentation::from_base("Mass"),
        0.001,
        Unit::from_base_unit("kg"),
    );
    add_derived_alias(&mut reg, "gram", "Mass", Unit::from_base_unit("g"));
    add_derived_alias(&mut reg, "grams", "Mass", Unit::from_base_unit("g"));

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

    // Pressure: Pa = N/m²
    reg.dimensions.add_base_dimension("Pressure");
    reg.add_derived_unit(
        "Pa",
        BaseRepresentation::from_base("Pressure"),
        1.0,
        Unit::from_base_unit("N").div(&Unit::from_base_unit("m").powi(2)),
    );

    // Power: W = J/s
    reg.dimensions.add_base_dimension("Power");
    reg.add_derived_unit(
        "W",
        BaseRepresentation::from_base("Power"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("s")),
    );
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
    add_derived_alias(&mut reg, "coulombs", "ElectricCharge", Unit::from_base_unit("C"));

    // Voltage: V = J/C = W/A
    reg.dimensions.add_base_dimension("Voltage");
    reg.add_derived_unit(
        "V",
        BaseRepresentation::from_base("Voltage"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("C")),
    );
    add_derived_alias(&mut reg, "volt", "Voltage", Unit::from_base_unit("V"));
    add_derived_alias(&mut reg, "volts", "Voltage", Unit::from_base_unit("V"));

    // Capacitance: F = C/V
    reg.dimensions.add_base_dimension("Capacitance");
    reg.add_derived_unit(
        "F",
        BaseRepresentation::from_base("Capacitance"),
        1.0,
        Unit::from_base_unit("C").div(&Unit::from_base_unit("V")),
    );
    add_derived_alias(&mut reg, "farad", "Capacitance", Unit::from_base_unit("F"));
    add_derived_alias(&mut reg, "farads", "Capacitance", Unit::from_base_unit("F"));

    // Resistance: ohm = V/A (symbol Ω not in Ident, use "ohm")
    reg.dimensions.add_base_dimension("Resistance");
    reg.add_derived_unit(
        "ohm",
        BaseRepresentation::from_base("Resistance"),
        1.0,
        Unit::from_base_unit("V").div(&Unit::from_base_unit("A")),
    );
    add_derived_alias(&mut reg, "ohms", "Resistance", Unit::from_base_unit("ohm"));

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
    add_derived_alias(&mut reg, "webers", "MagneticFlux", Unit::from_base_unit("Wb"));

    // Magnetic flux density: T = Wb/m²
    reg.dimensions.add_base_dimension("MagneticFluxDensity");
    reg.add_derived_unit(
        "T",
        BaseRepresentation::from_base("MagneticFluxDensity"),
        1.0,
        Unit::from_base_unit("Wb").div(&Unit::from_base_unit("m").powi(2)),
    );
    add_derived_alias(&mut reg, "tesla", "MagneticFluxDensity", Unit::from_base_unit("T"));
    add_derived_alias(&mut reg, "teslas", "MagneticFluxDensity", Unit::from_base_unit("T"));

    // Inductance: H = Wb/A
    reg.dimensions.add_base_dimension("Inductance");
    reg.add_derived_unit(
        "H",
        BaseRepresentation::from_base("Inductance"),
        1.0,
        Unit::from_base_unit("Wb").div(&Unit::from_base_unit("A")),
    );
    add_derived_alias(&mut reg, "henry", "Inductance", Unit::from_base_unit("H"));
    add_derived_alias(&mut reg, "henrys", "Inductance", Unit::from_base_unit("H"));

    // Luminous flux: lm = cd (steradian is dimensionless)
    reg.dimensions.add_base_dimension("LuminousFlux");
    reg.add_derived_unit(
        "lm",
        BaseRepresentation::from_base("LuminousFlux"),
        1.0,
        Unit::from_base_unit("cd"),
    );
    add_derived_alias(&mut reg, "lumen", "LuminousFlux", Unit::from_base_unit("lm"));
    add_derived_alias(&mut reg, "lumens", "LuminousFlux", Unit::from_base_unit("lm"));

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
    add_derived_alias(&mut reg, "becquerels", "Activity", Unit::from_base_unit("Bq"));

    // Absorbed dose: Gy = J/kg
    reg.dimensions.add_base_dimension("AbsorbedDose");
    reg.add_derived_unit(
        "Gy",
        BaseRepresentation::from_base("AbsorbedDose"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("kg")),
    );
    add_derived_alias(&mut reg, "gray", "AbsorbedDose", Unit::from_base_unit("Gy"));
    add_derived_alias(&mut reg, "grays", "AbsorbedDose", Unit::from_base_unit("Gy"));

    // Equivalent dose: Sv = J/kg (same dimension as Gy, different quantity type)
    reg.dimensions.add_base_dimension("EquivalentDose");
    reg.add_derived_unit(
        "Sv",
        BaseRepresentation::from_base("EquivalentDose"),
        1.0,
        Unit::from_base_unit("joule").div(&Unit::from_base_unit("kg")),
    );
    add_derived_alias(&mut reg, "sievert", "EquivalentDose", Unit::from_base_unit("Sv"));
    add_derived_alias(&mut reg, "sieverts", "EquivalentDose", Unit::from_base_unit("Sv"));

    // Catalytic activity: kat = mol/s
    reg.dimensions.add_base_dimension("CatalyticActivity");
    reg.add_derived_unit(
        "kat",
        BaseRepresentation::from_base("CatalyticActivity"),
        1.0,
        Unit::from_base_unit("mol").div(&Unit::from_base_unit("s")),
    );
    add_derived_alias(&mut reg, "katal", "CatalyticActivity", Unit::from_base_unit("kat"));
    add_derived_alias(&mut reg, "katals", "CatalyticActivity", Unit::from_base_unit("kat"));

    // Degree Celsius: same dimension as K, factor 1 (offset 273.15 not modeled)
    add_derived_alias(&mut reg, "celsius", "Temperature", Unit::from_base_unit("K"));

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
    fn angle_rad_degree_same_dimension_and_convert() {
        let reg = default_si_registry();
        let rad = Unit::from_base_unit("rad");
        let degree = Unit::from_base_unit("degree");
        assert!(reg.same_dimension(&rad, &degree).unwrap());
        let q_180_deg = Quantity::new(180.0, degree);
        let as_rad = q_180_deg.convert_to(&reg, &rad).unwrap();
        assert!((as_rad.value() - std::f64::consts::PI).abs() < 1e-10, "180 degree = π rad");
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

    /// Numbat supports many more units (week, year, inch, etc.). We treat unknown identifiers
    /// as symbols, so run() succeeds with Value::Symbolic; run_numeric() fails with SymbolHasNoValue.
    #[test]
    fn numbat_units_we_do_not_support_treated_as_symbols() {
        use crate::Value;
        let unsupported = ["week", "year", "inch", "foot", "pound"];
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
