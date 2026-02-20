//! Units: product of unit factors (with prefix and rational exponent).
//! Supports base and derived units; conversion via to_base_unit_representation.

use crate::dimension::Exponent;
use crate::prefix::Prefix;
use num_rational::Ratio;
use std::cmp::Ordering;
use std::collections::BTreeMap;

/// A single factor in a unit product: (unit name, prefix, exponent).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct UnitFactor {
    pub unit_name: String,
    pub prefix: Prefix,
    pub exponent: Exponent,
}

impl UnitFactor {
    pub fn new(unit_name: impl Into<String>, prefix: Prefix, exponent: Exponent) -> Self {
        Self {
            unit_name: unit_name.into(),
            prefix,
            exponent,
        }
    }

    pub fn merge_key(&self) -> (Prefix, &str) {
        (self.prefix, self.unit_name.as_str())
    }

    pub fn with_exponent(self, e: Exponent) -> Self {
        Self {
            exponent: self.exponent + e,
            ..self
        }
    }

    pub fn power(self, e: Exponent) -> Self {
        Self {
            exponent: self.exponent * e,
            ..self
        }
    }
}

impl PartialOrd for UnitFactor {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for UnitFactor {
    fn cmp(&self, other: &Self) -> Ordering {
        self.merge_key().cmp(&other.merge_key())
    }
}

/// Unit = product of unit factors. Stored in canonical form.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Unit {
    factors: Vec<UnitFactor>,
}

impl Unit {
    /// Dimensionless unit.
    pub fn scalar() -> Self {
        Self {
            factors: Vec::new(),
        }
    }

    pub fn is_scalar(&self) -> bool {
        self.factors.is_empty()
    }

    /// Single factor (no prefix, exponent 1).
    pub fn from_base_unit(unit_name: impl Into<String>) -> Self {
        Self {
            factors: vec![UnitFactor::new(
                unit_name,
                Prefix::none(),
                Exponent::from_integer(1),
            )],
        }
    }

    pub fn from_factor(f: UnitFactor) -> Self {
        if f.exponent == Ratio::from_integer(0) {
            return Self::scalar();
        }
        Self {
            factors: vec![f],
        }
    }

    /// Build from factors and canonicalize (merge same prefix+name, drop zero exponent).
    pub fn from_factors(factors: impl IntoIterator<Item = UnitFactor>) -> Self {
        let mut by_key: BTreeMap<(Prefix, String), Exponent> = BTreeMap::new();
        for f in factors {
            if f.exponent != Ratio::from_integer(0) {
                let key = (f.prefix, f.unit_name);
                let e = by_key.entry(key).or_insert_with(|| Ratio::from_integer(0));
                *e += f.exponent;
            }
        }
        by_key.retain(|_, e| *e != Ratio::from_integer(0));
        let factors = by_key
            .into_iter()
            .map(|((prefix, unit_name), exponent)| UnitFactor {
                unit_name,
                prefix,
                exponent,
            })
            .collect();
        Self { factors }
    }

    pub fn iter(&self) -> impl Iterator<Item = &UnitFactor> {
        self.factors.iter()
    }

    /// Multiply two units (concatenate and canonicalize).
    #[allow(clippy::should_implement_trait)]
    pub fn mul(mut self, other: &Self) -> Self {
        self.factors.extend(other.factors.clone());
        Self::from_factors(self.factors)
    }

    /// Divide: self * other^(-1).
    #[allow(clippy::should_implement_trait)]
    pub fn div(self, other: &Self) -> Self {
        let inv: Vec<UnitFactor> = other
            .iter()
            .map(|f| f.clone().power(Exponent::from_integer(-1)))
            .collect();
        self.mul(&Self::from_factors(inv))
    }

    /// Raise unit to integer power.
    pub fn powi(self, n: i64) -> Self {
        self.power(Exponent::from_integer(n))
    }

    /// Raise unit to rational power.
    pub fn power(self, exp: Exponent) -> Self {
        Self::from_factors(
            self.factors
                .into_iter()
                .map(|f| f.power(exp))
                .collect::<Vec<_>>(),
        )
    }

    /// Apply prefix to the first factor (for building e.g. km from m).
    pub fn with_prefix(mut self, prefix: Prefix) -> Self {
        if self.factors.is_empty() {
            return self;
        }
        self.factors[0].prefix = prefix;
        self
    }

    /// Strip prefixes from all factors.
    pub fn without_prefixes(&self) -> Self {
        Self::from_factors(self.iter().map(|f| UnitFactor {
            prefix: Prefix::none(),
            ..f.clone()
        }))
    }

    /// Common factors of two units: for each (prefix, unit_name) in both, take the exponent
    /// that divides both (min of positive exponents, max of negative). Used to optimize
    /// convert_to so e.g. km/h → mile/h only converts the length part.
    pub fn common_factors(a: &Self, b: &Self) -> Self {
        let a_map: std::collections::BTreeMap<_, _> = a
            .iter()
            .map(|f| ((f.prefix, f.unit_name.clone()), f.exponent))
            .collect();
        let mut out = Vec::new();
        for f in b.iter() {
            let key = (f.prefix, f.unit_name.clone());
            if let Some(&e_a) = a_map.get(&key) {
                let e_b = f.exponent;
                let common = if e_a > Ratio::from_integer(0) && e_b > Ratio::from_integer(0) {
                    std::cmp::min(e_a, e_b)
                } else if e_a < Ratio::from_integer(0) && e_b < Ratio::from_integer(0) {
                    std::cmp::max(e_a, e_b)
                } else {
                    continue;
                };
                if common != Ratio::from_integer(0) {
                    out.push(UnitFactor::new(f.unit_name.clone(), f.prefix, common));
                }
            }
        }
        Self::from_factors(out)
    }
}

impl std::fmt::Display for Unit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.factors.is_empty() {
            return Ok(());
        }
        let pos: Vec<_> = self.factors.iter().filter(|x| x.exponent > Ratio::from_integer(0)).collect();
        let neg: Vec<_> = self.factors.iter().filter(|x| x.exponent < Ratio::from_integer(0)).collect();
        // When in_denominator is true, show exponent as positive (e.g. "hour" not "hour⁻¹") since the slash already means "per".
        let fmt_one = |factors: &[&UnitFactor], in_denominator: bool| {
            factors
                .iter()
                .map(|f| {
                    let symbol = if f.prefix.is_none() {
                        f.unit_name.clone()
                    } else {
                        format!("{}{}", f.prefix.short_symbol(), f.unit_name)
                    };
                    let e = f.exponent;
                    let display_exp = if in_denominator { -e } else { e };
                    if display_exp == Ratio::from_integer(1) {
                        symbol
                    } else if display_exp == Ratio::from_integer(-1) {
                        format!("{symbol}⁻¹")
                    } else {
                        format!("{symbol}^{display_exp}")
                    }
                })
                .collect::<Vec<_>>()
                .join("·")
        };
        if neg.is_empty() {
            write!(f, "{}", fmt_one(&pos, false))
        } else if pos.is_empty() {
            write!(f, "1/{}", fmt_one(&neg, true))
        } else {
            write!(f, "{}/{}", fmt_one(&pos, false), fmt_one(&neg, true))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unit_scalar() {
        assert!(Unit::scalar().is_scalar());
    }

    #[test]
    fn unit_from_base() {
        let m = Unit::from_base_unit("m");
        assert!(!m.is_scalar());
        assert_eq!(m.iter().count(), 1);
        assert_eq!(m.iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn unit_mul_div() {
        let m = Unit::from_base_unit("m");
        let s = Unit::from_base_unit("s");
        let v = m.clone().div(&s);
        assert_eq!(v.iter().count(), 2);
    }

    #[test]
    fn unit_powi() {
        let m = Unit::from_base_unit("m");
        let m2 = m.powi(2);
        let v: Vec<_> = m2.iter().collect();
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].exponent, Ratio::from_integer(2));
    }

    #[test]
    fn unit_common_factors() {
        let km_h = Unit::from_base_unit("km").div(&Unit::from_base_unit("hour"));
        let mile_h = Unit::from_base_unit("mile").div(&Unit::from_base_unit("hour"));
        let common = Unit::common_factors(&km_h, &mile_h);
        assert_eq!(common.iter().count(), 1);
        assert_eq!(common.iter().next().unwrap().unit_name, "hour");
        assert_eq!(common.iter().next().unwrap().exponent, Ratio::from_integer(-1));
    }

    #[test]
    fn unit_display_division_no_redundant_inverse() {
        // Denominator factors are shown without ⁻¹ since the slash already means "per".
        let km_h = Unit::from_base_unit("km").div(&Unit::from_base_unit("hour"));
        assert_eq!(km_h.to_string(), "km/hour");
        let kilometers_hour = Unit::from_base_unit("kilometers").div(&Unit::from_base_unit("hour"));
        assert_eq!(kilometers_hour.to_string(), "kilometers/hour");
    }
}
