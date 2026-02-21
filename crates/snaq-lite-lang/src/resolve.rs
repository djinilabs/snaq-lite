//! Resolve parsed expression (LitScalar, LitWithUnit, LitUnit) to Lit(Quantity) or LitSymbol.
//! Identifiers that are units resolve to quantities; others resolve to symbols.

use crate::error::RunError;
use crate::ir::{CallArg, ExprDef};
use crate::quantity::Quantity;
use crate::unit_registry::UnitRegistry;

/// Convert parsed ExprDef (with LitScalar, LitWithUnit, LitUnit) to fully resolved ExprDef (Lit(Quantity), LitSymbol, or compound).
pub fn resolve(def: ExprDef, registry: &UnitRegistry) -> Result<ExprDef, RunError> {
    match def {
        ExprDef::LitScalar(n) => Ok(ExprDef::Lit(Quantity::from_scalar(n.0))),
        ExprDef::LitWithUnit(n, ref name) => {
            if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(ExprDef::Lit(Quantity::new(n.0, unit)))
            } else {
                Ok(ExprDef::Mul(
                    Box::new(ExprDef::Lit(Quantity::from_scalar(n.0))),
                    Box::new(ExprDef::LitSymbol(name.clone())),
                ))
            }
        }
        ExprDef::LitUnit(ref name) => {
            if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(ExprDef::Lit(Quantity::new(1.0, unit)))
            } else {
                Ok(ExprDef::LitSymbol(name.clone()))
            }
        }
        ExprDef::Lit(_) | ExprDef::LitSymbol(_) => Ok(def),
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
        ExprDef::Call(name, args) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok::<CallArg, RunError>(match arg {
                        CallArg::Positional(e) => CallArg::Positional(Box::new(resolve(*e, registry)?)),
                        CallArg::Named(n, e) => CallArg::Named(n, Box::new(resolve(*e, registry)?)),
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::Call(name, args))
        }
    }
}
