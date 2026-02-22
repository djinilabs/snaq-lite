//! Quantity: value + unit. Arithmetic with dimension checking and conversion.
//! Numeric values are SnaqNumber (value + variance) with variance propagation through arithmetic.

use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;
use ordered_float::OrderedFloat;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// A numeric value with associated variance (uncertainty²).
/// Infinite values (±∞) have variance 0.
///
/// Variance is propagated through arithmetic for uncorrelated operands:
/// - **Add/Sub:** Var(A ± B) = Var(A) + Var(B)
/// - **Mul:** Var(A×B) = B² Var(A) + A² Var(B)
/// - **Div:** Var(A/B) = (1/B²) Var(A) + (A²/B⁴) Var(B)
/// - **Scale by k:** Var(k×A) = k² Var(A)
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SnaqNumber {
    value: OrderedFloat<f64>,
    variance: OrderedFloat<f64>,
}

impl SnaqNumber {
    /// Create from a literal f64; variance is derived from representable precision
    /// (half-ulp in relative terms: (value * ε/2)² for finite non-zero; 0 for zero and ±∞).
    pub fn from_literal(x: f64) -> Self {
        let value = OrderedFloat::from(x);
        let variance = if x == 0.0 || x.is_infinite() {
            0.0
        } else {
            (x.abs() * f64::EPSILON / 2.0).powi(2)
        };
        Self {
            value,
            variance: OrderedFloat::from(variance),
        }
    }

    /// Create with explicit value and variance (for tests and internal use).
    pub fn new(value: f64, variance: f64) -> Self {
        Self {
            value: OrderedFloat::from(value),
            variance: OrderedFloat::from(variance.max(0.0)),
        }
    }

    pub fn value(&self) -> f64 {
        self.value.0
    }

    pub fn variance(&self) -> f64 {
        self.variance.0
    }

    /// Standard deviation (sqrt of variance).
    pub fn std_dev(&self) -> f64 {
        self.variance.0.sqrt()
    }
}

impl Add for SnaqNumber {
    type Output = SnaqNumber;

    fn add(self, rhs: SnaqNumber) -> Self::Output {
        SnaqNumber {
            value: OrderedFloat::from(self.value.0 + rhs.value.0),
            variance: OrderedFloat::from(self.variance.0 + rhs.variance.0),
        }
    }
}

impl Sub for SnaqNumber {
    type Output = SnaqNumber;

    fn sub(self, rhs: SnaqNumber) -> Self::Output {
        SnaqNumber {
            value: OrderedFloat::from(self.value.0 - rhs.value.0),
            variance: OrderedFloat::from(self.variance.0 + rhs.variance.0),
        }
    }
}

impl Mul for SnaqNumber {
    type Output = SnaqNumber;

    fn mul(self, rhs: SnaqNumber) -> Self::Output {
        let a = self.value.0;
        let b = rhs.value.0;
        let var_a = self.variance.0;
        let var_b = rhs.variance.0;
        // Var(A*B) = B² Var(A) + A² Var(B)
        let variance = (b * b * var_a + a * a * var_b).max(0.0);
        SnaqNumber {
            value: OrderedFloat::from(a * b),
            variance: OrderedFloat::from(variance),
        }
    }
}

impl Div for SnaqNumber {
    type Output = SnaqNumber;

    fn div(self, rhs: SnaqNumber) -> Self::Output {
        let a = self.value.0;
        let b = rhs.value.0;
        let var_a = self.variance.0;
        let var_b = rhs.variance.0;
        // Var(A/B) = (1/B²) Var(A) + (A²/B⁴) Var(B)
        let variance = ((1.0 / (b * b)) * var_a + (a * a) / (b * b * b * b) * var_b).max(0.0);
        SnaqNumber {
            value: OrderedFloat::from(a / b),
            variance: OrderedFloat::from(variance),
        }
    }
}

impl Neg for SnaqNumber {
    type Output = SnaqNumber;

    fn neg(self) -> Self::Output {
        SnaqNumber {
            value: OrderedFloat::from(-self.value.0),
            variance: self.variance,
        }
    }
}

impl Mul<f64> for SnaqNumber {
    type Output = SnaqNumber;

    fn mul(self, k: f64) -> Self::Output {
        let variance = (self.variance.0 * k * k).max(0.0);
        SnaqNumber {
            value: OrderedFloat::from(self.value.0 * k),
            variance: OrderedFloat::from(variance),
        }
    }
}

impl Div<f64> for SnaqNumber {
    type Output = SnaqNumber;

    fn div(self, k: f64) -> Self::Output {
        let inv = 1.0 / k;
        let variance = (self.variance.0 * inv * inv).max(0.0);
        SnaqNumber {
            value: OrderedFloat::from(self.value.0 * inv),
            variance: OrderedFloat::from(variance),
        }
    }
}

/// Result of quantity operations that can fail (dimension mismatch, incompatible units, or 0/0).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantityError {
    DimensionMismatch { left: Unit, right: Unit },
    /// Indeterminate form 0/0 (nonzero/0 yields ±∞ and does not error).
    DivisionByZero,
    IncompatibleUnits(Unit, Unit),
}

impl std::fmt::Display for QuantityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QuantityError::DimensionMismatch { left, right } => {
                write!(f, "dimension mismatch: {left} vs {right}")
            }
            QuantityError::DivisionByZero => write!(f, "division by zero"),
            QuantityError::IncompatibleUnits(a, b) => {
                write!(f, "incompatible units: {a} vs {b}")
            }
        }
    }
}

impl std::error::Error for QuantityError {}

/// A physical quantity: numeric value (with variance) and unit.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Quantity {
    pub number: SnaqNumber,
    pub unit: Unit,
}

impl Quantity {
    /// Create a quantity from a literal f64 (variance derived from representation precision).
    pub fn new(value: f64, unit: Unit) -> Self {
        Self {
            number: SnaqNumber::from_literal(value),
            unit,
        }
    }

    /// Create a quantity from an existing SnaqNumber (e.g. result of arithmetic).
    pub fn with_number(number: SnaqNumber, unit: Unit) -> Self {
        Self { number, unit }
    }

    pub fn from_scalar(value: f64) -> Self {
        Self {
            number: SnaqNumber::from_literal(value),
            unit: Unit::scalar(),
        }
    }

    /// Numeric value (mean).
    pub fn value(&self) -> f64 {
        self.number.value()
    }

    /// Variance of the numeric value (uncertainty²), propagated through arithmetic.
    pub fn variance(&self) -> f64 {
        self.number.variance()
    }

    pub fn unit(&self) -> &Unit {
        &self.unit
    }

    pub fn is_zero(&self) -> bool {
        self.number.value() == 0.0
    }

    /// True if the numeric value is +∞ or -∞.
    pub fn is_infinite(&self) -> bool {
        self.number.value().is_infinite()
    }

    /// True if the numeric value is finite (not ±∞ and not NaN).
    pub fn is_finite(&self) -> bool {
        self.number.value().is_finite()
    }

    /// Extract numeric value if dimensionless; error otherwise.
    pub fn as_scalar(&self) -> Result<f64, QuantityError> {
        if self.unit.is_scalar() {
            Ok(self.number.value())
        } else {
            Err(QuantityError::IncompatibleUnits(
                self.unit.clone(),
                Unit::scalar(),
            ))
        }
    }

    /// Choose the unit with the smaller conversion factor to base (for add/sub commutativity).
    pub fn smaller_unit<'a>(
        registry: &UnitRegistry,
        a: &'a Unit,
        b: &'a Unit,
    ) -> Option<&'a Unit> {
        let (_, fa) = registry.to_base_unit_representation(a)?;
        let (_, fb) = registry.to_base_unit_representation(b)?;
        if fa <= fb {
            Some(a)
        } else {
            Some(b)
        }
    }

    /// Simplify: if dimensionally equivalent to scalar, return scalar quantity.
    pub fn full_simplify(&self, registry: &UnitRegistry) -> Quantity {
        match registry.to_base_unit_representation(&self.unit) {
            Some((base_unit, factor)) if base_unit.is_scalar() => {
                Quantity::with_number(self.number * factor, Unit::scalar())
            }
            _ => self.clone(),
        }
    }

    /// After full_simplify, try to express in a registered derived unit that is *definitionally*
    /// equivalent (same conversion factor to base), e.g. J/s → W. Only simplifies when the
    /// unit's factor to base matches the candidate's factor (Numbat-style); does not simplify
    /// to merely dimensionally equivalent units (e.g. Wh/W ≠ century).
    pub fn full_simplify_with_registry(&self, registry: &UnitRegistry) -> Quantity {
        let q = self.full_simplify(registry);
        if q.unit.is_scalar() {
            return q;
        }
        let (_, source_factor) = match registry.to_base_unit_representation(&q.unit) {
            Some(x) => x,
            None => return q,
        };
        let current_complexity = q.unit.iter().count();
        let mut best: Option<Quantity> = None;
        for name in registry.unit_names() {
            let u = match registry.get_unit_with_prefix(name) {
                Some(unit) => unit,
                None => continue,
            };
            if !registry.same_dimension(&q.unit, &u).unwrap_or(false) {
                continue;
            }
            let target_complexity = u.iter().count();
            if target_complexity >= current_complexity {
                continue;
            }
            let (_, target_factor) = match registry.to_base_unit_representation(&u) {
                Some(x) => x,
                None => continue,
            };
            let factors_match = (source_factor - target_factor).abs()
                < 1e-9 * source_factor.abs().max(1.0);
            if !factors_match {
                continue;
            }
            if let Ok(converted) = q.convert_to(registry, &u) {
                if best.as_ref().is_none_or(|b| converted.unit.iter().count() < b.unit.iter().count()) {
                    best = Some(converted.clone());
                    if target_complexity == 1 {
                        return converted;
                    }
                }
            }
        }
        best.unwrap_or(q)
    }

    /// Convert this quantity to the target unit. Same dimension required.
    /// Uses common-factor optimization (Numbat-style): when converting e.g. km/h to mile/h,
    /// only the length part is converted, leaving the "per hour" factor unchanged.
    /// Variance is propagated as Var(result) = ratio² × Var(self) via [SnaqNumber] scaling.
    pub fn convert_to(
        &self,
        registry: &UnitRegistry,
        target: &Unit,
    ) -> Result<Quantity, QuantityError> {
        if &self.unit == target || self.is_zero() {
            return Ok(Quantity::with_number(self.number, target.clone()));
        }
        if !registry.same_dimension(&self.unit, target).unwrap_or(false) {
            return Err(QuantityError::IncompatibleUnits(
                self.unit.clone(),
                target.clone(),
            ));
        }
        if self.is_infinite() {
            return Ok(Quantity::with_number(self.number, target.clone()));
        }

        let common = Unit::common_factors(&self.unit, target);
        if !common.is_scalar() {
            let self_reduced = self.unit.clone().div(&common);
            let target_reduced = target.clone().div(&common);
            if let Some((self_base, self_red_factor)) =
                registry.to_base_unit_representation(&self_reduced)
            {
                if let Some((target_base, target_red_factor)) =
                    registry.to_base_unit_representation(&target_reduced)
                {
                    if registry.same_dimension(&self_base, &target_base).unwrap_or(false) {
                        let ratio = self_red_factor / target_red_factor;
                        return Ok(Quantity::with_number(
                            self.number * ratio,
                            target.clone(),
                        ));
                    }
                }
            }
        }

        let (_, self_factor) = registry
            .to_base_unit_representation(&self.unit)
            .ok_or_else(|| QuantityError::IncompatibleUnits(self.unit.clone(), target.clone()))?;
        let (_, target_factor) = registry
            .to_base_unit_representation(target)
            .ok_or_else(|| QuantityError::IncompatibleUnits(self.unit.clone(), target.clone()))?;
        let ratio = self_factor / target_factor;
        Ok(Quantity::with_number(self.number * ratio, target.clone()))
    }

    /// Add two quantities; same dimension required. Uses smaller_unit for result.
    pub fn add(
        self,
        rhs: &Quantity,
        registry: &UnitRegistry,
    ) -> Result<Quantity, QuantityError> {
        if self.is_zero() {
            return Ok(rhs.clone());
        }
        if rhs.is_zero() {
            return Ok(self);
        }
        if !registry
            .same_dimension(&self.unit, &rhs.unit)
            .unwrap_or(false)
        {
            return Err(QuantityError::DimensionMismatch {
                left: self.unit,
                right: rhs.unit.clone(),
            });
        }
        let result_unit = Self::smaller_unit(registry, &self.unit, &rhs.unit).cloned().unwrap_or_else(|| self.unit.clone());
        let a = self.convert_to(registry, &result_unit)?;
        let b = rhs.convert_to(registry, &result_unit)?;
        Ok(Quantity::with_number(a.number + b.number, result_unit))
    }

    /// Subtract; same dimension required.
    pub fn sub(
        self,
        rhs: &Quantity,
        registry: &UnitRegistry,
    ) -> Result<Quantity, QuantityError> {
        if rhs.is_zero() {
            return Ok(self);
        }
        if self.is_zero() {
            return Ok(Quantity::with_number(-rhs.number, rhs.unit.clone()));
        }
        if !registry
            .same_dimension(&self.unit, &rhs.unit)
            .unwrap_or(false)
        {
            return Err(QuantityError::DimensionMismatch {
                left: self.unit,
                right: rhs.unit.clone(),
            });
        }
        let result_unit = Self::smaller_unit(registry, &self.unit, &rhs.unit).cloned().unwrap_or_else(|| self.unit.clone());
        let a = self.convert_to(registry, &result_unit)?;
        let b = rhs.convert_to(registry, &result_unit)?;
        Ok(Quantity::with_number(a.number - b.number, result_unit))
    }
}

impl Mul for Quantity {
    type Output = Quantity;

    fn mul(self, rhs: Quantity) -> Self::Output {
        Quantity::with_number(
            self.number * rhs.number,
            self.unit.clone().mul(&rhs.unit),
        )
    }
}

impl Div for Quantity {
    type Output = Result<Quantity, QuantityError>;

    /// Division: nonzero/0 → ±∞ (sign of numerator), 0/0 → DivisionByZero. Infinite values have variance 0.
    fn div(self, rhs: Quantity) -> Self::Output {
        let r = rhs.number.value();
        let s = self.number.value();
        if r == 0.0 {
            if s == 0.0 {
                return Err(QuantityError::DivisionByZero);
            }
            let inf = if s.is_sign_positive() {
                f64::INFINITY
            } else {
                f64::NEG_INFINITY
            };
            return Ok(Quantity::with_number(
                SnaqNumber::from_literal(inf),
                self.unit.clone().div(&rhs.unit),
            ));
        }
        Ok(Quantity::with_number(
            self.number / rhs.number,
            self.unit.clone().div(&rhs.unit),
        ))
    }
}

impl Neg for Quantity {
    type Output = Quantity;

    fn neg(self) -> Self::Output {
        Quantity::with_number(-self.number, self.unit)
    }
}

impl std::fmt::Display for Quantity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.unit.is_scalar() {
            write!(f, "{}", self.number.value())
        } else {
            write!(f, "{} {}", self.number.value(), self.unit)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::unit_registry::default_si_registry;

    #[test]
    fn quantity_scalar() {
        let q = Quantity::from_scalar(3.0);
        assert!(q.unit().is_scalar());
        assert_eq!(q.value(), 3.0);
    }

    #[test]
    fn quantity_add_same_unit() {
        let reg = default_si_registry();
        let a = Quantity::new(1.0, Unit::from_base_unit("m"));
        let b = Quantity::new(2.0, Unit::from_base_unit("m"));
        let c = a.add(&b, &reg).unwrap();
        assert_eq!(c.value(), 3.0);
        assert_eq!(c.unit.iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn quantity_add_convert() {
        let reg = default_si_registry();
        let a = Quantity::new(1.0, Unit::from_base_unit("km"));
        let b = Quantity::new(500.0, Unit::from_base_unit("m"));
        let c = a.add(&b, &reg).unwrap();
        // 1 km + 500 m = 1500 m (smaller unit is m)
        assert!((c.value() - 1500.0).abs() < 1e-10);
        assert_eq!(c.unit.iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn quantity_mul_div() {
        let a = Quantity::new(10.0, Unit::from_base_unit("m"));
        let b = Quantity::new(2.0, Unit::from_base_unit("s"));
        let c = a * b.clone();
        assert_eq!(c.value(), 20.0);
        let d = (c / b).unwrap();
        assert_eq!(d.value(), 10.0);
        assert_eq!(d.unit.iter().next().unwrap().unit_name, "m");
    }

    #[test]
    fn quantity_convert_to() {
        let reg = default_si_registry();
        let q = Quantity::new(1.0, Unit::from_base_unit("km"));
        let as_m = q.convert_to(&reg, &Unit::from_base_unit("m")).unwrap();
        assert!((as_m.value() - 1000.0).abs() < 1e-10);
    }

    #[test]
    fn quantity_convert_to_propagates_variance() {
        let reg = default_si_registry();
        let q = Quantity::with_number(
            SnaqNumber::new(10.0, 0.25),
            Unit::from_base_unit("km"),
        );
        let as_m = q.convert_to(&reg, &Unit::from_base_unit("m")).unwrap();
        assert!((as_m.value() - 10_000.0).abs() < 1e-10);
        // ratio = 1000 (km → m), so Var(result) = 1000² × 0.25 = 250_000
        assert!((as_m.variance() - 250_000.0).abs() < 1e-6);
    }

    #[test]
    fn quantity_convert_to_common_factor_optimization() {
        let reg = default_si_registry();
        let km_h = Unit::from_base_unit("km").div(&Unit::from_base_unit("hour"));
        let mile_h = Unit::from_base_unit("mile").div(&Unit::from_base_unit("hour"));
        let q = Quantity::new(1.0, km_h);
        let c = q.convert_to(&reg, &mile_h).unwrap();
        assert!((c.value() - 1.0 / 1.609_344).abs() < 1e-6, "1 km/h = 1/1.609344 mile/h");
        assert_eq!(c.unit().iter().count(), 2);
    }

    #[test]
    fn quantity_full_simplify_dimensionless() {
        let reg = default_si_registry();
        let m = Unit::from_base_unit("m");
        let q = Quantity::new(10.0, m.clone()).div(Quantity::new(2.0, m)).unwrap();
        let simplified = q.full_simplify(&reg);
        assert!(simplified.unit().is_scalar());
        assert!((simplified.value() - 5.0).abs() < 1e-10);
    }

    #[test]
    fn quantity_full_simplify_with_registry() {
        let reg = default_si_registry();
        let q = Quantity::new(3600.0, Unit::from_base_unit("s"));
        let simplified = q.full_simplify_with_registry(&reg);
        assert!(reg.same_dimension(simplified.unit(), &Unit::from_base_unit("s")).unwrap());
        assert!((simplified.value() - 3600.0).abs() < 1e-6, "no definitionally simpler unit for 3600 s");
    }

    #[test]
    fn quantity_full_simplify_with_registry_definitional() {
        let reg = default_si_registry();
        let j_per_s = Unit::from_base_unit("joule").div(&Unit::from_base_unit("s"));
        let q = Quantity::new(1.0, j_per_s);
        let simplified = q.full_simplify_with_registry(&reg);
        assert_eq!(simplified.unit().iter().next().unwrap().unit_name, "W");
        assert!((simplified.value() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn quantity_div_by_zero_nonzero_yields_infinity() {
        let zero = Quantity::from_scalar(0.0);
        let pos = Quantity::from_scalar(1.0);
        let neg = Quantity::from_scalar(-3.0);
        let pos_inf = (pos / zero.clone()).unwrap();
        assert_eq!(pos_inf.value(), f64::INFINITY);
        assert_eq!(pos_inf.variance(), 0.0);
        let neg_inf = (neg / zero).unwrap();
        assert_eq!(neg_inf.value(), f64::NEG_INFINITY);
        assert_eq!(neg_inf.variance(), 0.0);
    }

    #[test]
    fn quantity_div_zero_by_zero_returns_err() {
        let zero = Quantity::from_scalar(0.0);
        let e = zero.clone() / zero;
        assert!(e.is_err());
        assert!(matches!(e.unwrap_err(), QuantityError::DivisionByZero));
    }

    #[test]
    fn quantity_div_by_zero_with_units() {
        let reg = default_si_registry();
        let m = Unit::from_base_unit("m");
        let s = Unit::from_base_unit("s");
        let q = Quantity::new(3.0, m.clone());
        let zero_s = Quantity::new(0.0, s.clone());
        let result = (q / zero_s).unwrap();
        assert_eq!(result.value(), f64::INFINITY);
        assert!(result.is_infinite());
        assert!(!result.is_finite());
        assert!(reg.same_dimension(result.unit(), &m.div(&s)).unwrap());
    }

    #[test]
    fn quantity_convert_to_preserves_infinity() {
        let reg = default_si_registry();
        let inf_km = Quantity::with_number(
            SnaqNumber::from_literal(f64::INFINITY),
            Unit::from_base_unit("km"),
        );
        let as_m = inf_km.convert_to(&reg, &Unit::from_base_unit("m")).unwrap();
        assert_eq!(as_m.value(), f64::INFINITY);
        assert!(as_m.is_infinite());
    }
}

#[cfg(test)]
mod snaq_number_tests {
    use super::SnaqNumber;

    #[test]
    fn snaq_number_from_literal_zero_has_zero_variance() {
        let n = SnaqNumber::from_literal(0.0);
        assert_eq!(n.value(), 0.0);
        assert_eq!(n.variance(), 0.0);
    }

    #[test]
    fn snaq_number_from_literal_nonzero_has_positive_variance() {
        let n = SnaqNumber::from_literal(1.0);
        assert_eq!(n.value(), 1.0);
        assert!(n.variance() > 0.0);
        assert!(n.variance() < 1e-20); // small relative to 1
    }

    #[test]
    fn snaq_number_from_literal_infinite_has_zero_variance() {
        let pos = SnaqNumber::from_literal(f64::INFINITY);
        assert_eq!(pos.value(), f64::INFINITY);
        assert_eq!(pos.variance(), 0.0);
        let neg = SnaqNumber::from_literal(f64::NEG_INFINITY);
        assert_eq!(neg.value(), f64::NEG_INFINITY);
        assert_eq!(neg.variance(), 0.0);
    }

    #[test]
    fn snaq_number_add_sub_variance() {
        let a = SnaqNumber::new(3.0, 1.0);
        let b = SnaqNumber::new(2.0, 0.5);
        let sum = a + b;
        assert_eq!(sum.value(), 5.0);
        assert_eq!(sum.variance(), 1.5);
        let diff = a - b;
        assert_eq!(diff.value(), 1.0);
        assert_eq!(diff.variance(), 1.5);
    }

    #[test]
    fn snaq_number_mul_div_variance() {
        let a = SnaqNumber::new(10.0, 0.1);
        let b = SnaqNumber::new(2.0, 0.2);
        let prod = a * b;
        assert_eq!(prod.value(), 20.0);
        // Var(A*B) = B² Var(A) + A² Var(B) = 4*0.1 + 100*0.2 = 20.4
        assert!((prod.variance() - 20.4).abs() < 1e-10);
        let quot = a / b;
        assert_eq!(quot.value(), 5.0);
        // Var(A/B) = (1/B²)Var(A) + (A²/B⁴)Var(B) = 0.1/4 + 100/16*0.2 = 0.025 + 1.25 = 1.275
        assert!((quot.variance() - 1.275).abs() < 1e-10);
    }

    #[test]
    fn snaq_number_neg_preserves_variance() {
        let a = SnaqNumber::new(3.0, 2.0);
        let n = -a;
        assert_eq!(n.value(), -3.0);
        assert_eq!(n.variance(), 2.0);
    }

    #[test]
    fn snaq_number_scale_by_f64() {
        let a = SnaqNumber::new(5.0, 1.0);
        let scaled = a * 10.0;
        assert_eq!(scaled.value(), 50.0);
        assert_eq!(scaled.variance(), 100.0);
        let div = a / 2.0;
        assert_eq!(div.value(), 2.5);
        assert_eq!(div.variance(), 0.25);
    }

    #[test]
    fn snaq_number_variance_always_non_negative() {
        // Operations should never produce negative variance (float noise clamp).
        let a = SnaqNumber::from_literal(1e-20);
        let b = SnaqNumber::from_literal(1e20);
        assert!(a.variance() >= 0.0);
        assert!(b.variance() >= 0.0);
        let prod = a * b;
        let quot = a / b;
        assert!(prod.variance() >= 0.0, "mul variance {}", prod.variance());
        assert!(quot.variance() >= 0.0, "div variance {}", quot.variance());
    }
}
