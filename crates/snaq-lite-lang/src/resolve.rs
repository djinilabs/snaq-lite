//! Resolve parsed expression (LitScalar, LitWithUnit, LitUnit) to Lit(Quantity).

use crate::error::RunError;
use crate::ir::ExprDef;
use crate::quantity::Quantity;
use crate::unit_registry::UnitRegistry;

/// Convert parsed ExprDef (with LitScalar, LitWithUnit, LitUnit) to fully resolved ExprDef (only Lit(Quantity) for literals).
pub fn resolve(def: ExprDef, registry: &UnitRegistry) -> Result<ExprDef, RunError> {
    match def {
        ExprDef::LitScalar(n) => Ok(ExprDef::Lit(Quantity::from_scalar(n.0))),
        ExprDef::LitWithUnit(n, ref name) => {
            let unit = registry
                .get_unit_with_prefix(name)
                .ok_or_else(|| RunError::UnknownUnit(name.clone()))?;
            Ok(ExprDef::Lit(Quantity::new(n.0, unit)))
        }
        ExprDef::LitUnit(ref name) => {
            let unit = registry
                .get_unit_with_prefix(name)
                .ok_or_else(|| RunError::UnknownUnit(name.clone()))?;
            Ok(ExprDef::Lit(Quantity::new(1.0, unit)))
        }
        ExprDef::Lit(_) => Ok(def),
        ExprDef::Add(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Add(Box::new(l), Box::new(r)))
        }
        ExprDef::Sub(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Sub(Box::new(l), Box::new(r)))
        }
        ExprDef::Mul(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Mul(Box::new(l), Box::new(r)))
        }
        ExprDef::Div(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Div(Box::new(l), Box::new(r)))
        }
        ExprDef::Neg(inner) => {
            let inner = resolve(*inner, registry)?;
            Ok(ExprDef::Neg(Box::new(inner)))
        }
    }
}
