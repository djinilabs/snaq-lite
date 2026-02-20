//! Quantity: value + unit. Arithmetic with dimension checking and conversion.

use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;
use ordered_float::OrderedFloat;
use std::ops::{Div, Mul, Neg};

/// Result of quantity operations that can fail (dimension mismatch, division by zero).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantityError {
    DimensionMismatch { left: Unit, right: Unit },
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

/// A physical quantity: numeric value and unit.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Quantity {
    pub value: OrderedFloat<f64>,
    pub unit: Unit,
}

impl Quantity {
    pub fn new(value: f64, unit: Unit) -> Self {
        Self {
            value: OrderedFloat::from(value),
            unit,
        }
    }

    pub fn from_scalar(value: f64) -> Self {
        Self {
            value: OrderedFloat::from(value),
            unit: Unit::scalar(),
        }
    }

    pub fn value(&self) -> f64 {
        self.value.0
    }

    pub fn unit(&self) -> &Unit {
        &self.unit
    }

    pub fn is_zero(&self) -> bool {
        self.value.0 == 0.0
    }

    /// Extract numeric value if dimensionless; error otherwise.
    pub fn as_scalar(&self) -> Result<f64, QuantityError> {
        if self.unit.is_scalar() {
            Ok(self.value.0)
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
                Quantity::from_scalar(self.value.0 * factor)
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
    pub fn convert_to(
        &self,
        registry: &UnitRegistry,
        target: &Unit,
    ) -> Result<Quantity, QuantityError> {
        if &self.unit == target || self.is_zero() {
            return Ok(Quantity::new(self.value.0, target.clone()));
        }
        if !registry.same_dimension(&self.unit, target).unwrap_or(false) {
            return Err(QuantityError::IncompatibleUnits(
                self.unit.clone(),
                target.clone(),
            ));
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
                        let new_value =
                            self.value.0 * (self_red_factor / target_red_factor);
                        return Ok(Quantity::new(new_value, target.clone()));
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
        let new_value = self.value.0 * (self_factor / target_factor);
        Ok(Quantity::new(new_value, target.clone()))
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
        Ok(Quantity::new(a.value.0 + b.value.0, result_unit))
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
            return Ok(Quantity::new(-rhs.value.0, rhs.unit.clone()));
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
        Ok(Quantity::new(a.value.0 - b.value.0, result_unit))
    }
}

impl Mul for Quantity {
    type Output = Quantity;

    fn mul(self, rhs: Quantity) -> Self::Output {
        Quantity::new(
            self.value.0 * rhs.value.0,
            self.unit.clone().mul(&rhs.unit),
        )
    }
}

impl Div for Quantity {
    type Output = Result<Quantity, QuantityError>;

    fn div(self, rhs: Quantity) -> Self::Output {
        if rhs.value.0 == 0.0 {
            return Err(QuantityError::DivisionByZero);
        }
        Ok(Quantity::new(
            self.value.0 / rhs.value.0,
            self.unit.clone().div(&rhs.unit),
        ))
    }
}

impl Neg for Quantity {
    type Output = Quantity;

    fn neg(self) -> Self::Output {
        Quantity::new(-self.value.0, self.unit)
    }
}

impl std::fmt::Display for Quantity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.unit.is_scalar() {
            write!(f, "{}", self.value.0)
        } else {
            write!(f, "{} {}", self.value.0, self.unit)
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
}
