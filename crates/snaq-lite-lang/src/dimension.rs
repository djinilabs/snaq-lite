//! Dimensions: base and derived, with rational exponents.
//! Used to check that addition/subtraction only happens for same dimension.

use num_rational::Ratio;
use std::collections::BTreeMap;

/// Rational exponent for dimensions (and units).
pub type Exponent = Ratio<i64>;

/// A dimension is a product of base-dimension names with rational exponents.
/// Stored in canonical form: sorted by name, zero exponents removed.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct BaseRepresentation(BTreeMap<String, Exponent>);

impl BaseRepresentation {
    /// Dimensionless (scalar).
    pub fn unity() -> Self {
        Self(BTreeMap::new())
    }

    /// Single base dimension with exponent 1.
    pub fn from_base(name: &str) -> Self {
        let mut m = BTreeMap::new();
        m.insert(name.to_string(), Exponent::from_integer(1));
        Self(m)
    }

    /// From a single (name, exponent) pair.
    pub fn from_factor(name: String, exp: Exponent) -> Self {
        if exp == Exponent::from_integer(0) {
            return Self::unity();
        }
        let mut m = BTreeMap::new();
        m.insert(name, exp);
        Self(m)
    }

    /// From multiple factors; merges same names, drops zero exponents.
    pub fn from_factors(factors: impl IntoIterator<Item = (String, Exponent)>) -> Self {
        let mut m = BTreeMap::new();
        for (name, exp) in factors {
            if exp != Exponent::from_integer(0) {
                let e = m.entry(name).or_insert_with(|| Exponent::from_integer(0));
                *e += exp;
            }
        }
        m.retain(|_, e| *e != Exponent::from_integer(0));
        Self(m)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &Exponent)> {
        self.0.iter().map(|(k, v)| (k.as_str(), v))
    }

    pub fn is_scalar(&self) -> bool {
        self.0.is_empty()
    }

    /// Multiply two base representations (add exponents for same base).
    #[allow(clippy::should_implement_trait)]
    pub fn mul(mut self, other: &Self) -> Self {
        for (name, exp) in &other.0 {
            if *exp != Exponent::from_integer(0) {
                *self.0.entry(name.clone()).or_insert_with(|| Exponent::from_integer(0)) =
                    self.0.get(name).copied().unwrap_or_else(|| Exponent::from_integer(0)) + *exp;
            }
        }
        self.0.retain(|_, e| *e != Exponent::from_integer(0));
        self
    }

    /// Divide: self * other^(-1).
    #[allow(clippy::should_implement_trait)]
    pub fn div(mut self, other: &Self) -> Self {
        for (name, exp) in &other.0 {
            *self.0.entry(name.clone()).or_insert_with(|| Exponent::from_integer(0)) =
                self.0.get(name).copied().unwrap_or_else(|| Exponent::from_integer(0)) - *exp;
        }
        self.0.retain(|_, e| *e != Exponent::from_integer(0));
        self
    }

    /// Raise to a rational power.
    pub fn power(&self, exp: Exponent) -> Self {
        let m = self
            .0
            .iter()
            .map(|(k, v)| (k.clone(), v * exp))
            .filter(|(_, e)| *e != Exponent::from_integer(0))
            .collect();
        Self(m)
    }
}

impl std::fmt::Display for BaseRepresentation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0.is_empty() {
            return f.write_str("Scalar");
        }
        let parts: Vec<String> = self
            .0
            .iter()
            .map(|(name, e)| {
                if *e == Exponent::from_integer(1) {
                    name.clone()
                } else {
                    format!("{name}^{e}")
                }
            })
            .collect();
        write!(f, "{}", parts.join("×"))
    }
}

/// Registry of base and derived dimensions.
#[derive(Clone, Default)]
pub struct DimensionRegistry {
    base: std::collections::HashMap<String, BaseRepresentation>,
    derived: std::collections::HashMap<String, BaseRepresentation>,
}

impl DimensionRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_base_dimension(&mut self, name: &str) {
        self.base
            .insert(name.to_string(), BaseRepresentation::from_base(name));
    }

    pub fn add_derived_dimension(&mut self, name: &str, repr: BaseRepresentation) {
        self.derived.insert(name.to_string(), repr);
    }

    pub fn get_base_representation(&self, name: &str) -> Option<&BaseRepresentation> {
        self.base.get(name).or_else(|| self.derived.get(name))
    }

    pub fn contains(&self, name: &str) -> bool {
        self.base.contains_key(name) || self.derived.contains_key(name)
    }

    pub fn is_base_dimension(&self, name: &str) -> bool {
        self.base.contains_key(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimension_unity() {
        let u = BaseRepresentation::unity();
        assert!(u.is_scalar());
        assert_eq!(u.iter().count(), 0);
    }

    #[test]
    fn dimension_from_base() {
        let l = BaseRepresentation::from_base("Length");
        assert!(!l.is_scalar());
        let v: Vec<_> = l.iter().collect();
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].0, "Length");
        assert_eq!(v[0].1, &Exponent::from_integer(1));
    }

    #[test]
    fn dimension_mul_div() {
        let l = BaseRepresentation::from_base("Length");
        let t = BaseRepresentation::from_base("Time");
        let v = l.clone().div(&t);
        let v_repr: Vec<_> = v.iter().collect();
        assert_eq!(v_repr.len(), 2);
        let length_exp = v_repr
            .iter()
            .find(|(n, _)| *n == "Length")
            .map(|(_, e)| (*e).clone());
        let time_exp = v_repr
            .iter()
            .find(|(n, _)| *n == "Time")
            .map(|(_, e)| (*e).clone());
        assert_eq!(length_exp, Some(Exponent::from_integer(1)));
        assert_eq!(time_exp, Some(Exponent::from_integer(-1)));
    }

    #[test]
    fn dimension_power() {
        let l = BaseRepresentation::from_base("Length");
        let l2 = l.power(Exponent::from_integer(2));
        let v: Vec<_> = l2.iter().collect();
        assert_eq!(v.len(), 1);
        assert_eq!(v[0].1, &Exponent::from_integer(2));
    }
}
