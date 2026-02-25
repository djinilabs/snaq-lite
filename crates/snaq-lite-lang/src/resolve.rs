//! Resolve parsed expression (LitScalar, LitWithUnit, LitUnit) to Lit(Quantity) or LitSymbol.
//! Identifiers that are units resolve to quantities; others resolve to symbols.

use crate::error::RunError;
use crate::ir::{CallArg, ExprDef};
use crate::quantity::{Quantity, SnaqNumber};
use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;

/// Convert parsed ExprDef (with LitScalar, LitWithUnit, LitUnit) to fully resolved ExprDef (Lit(Quantity), LitSymbol, or compound).
pub fn resolve(def: ExprDef, registry: &UnitRegistry) -> Result<ExprDef, RunError> {
    match def {
        ExprDef::LitScalar(n) => Ok(ExprDef::Lit(Quantity::with_number(
            SnaqNumber::new(n.value_f64(), n.implicit_variance()),
            Unit::scalar(),
        ))),
        ExprDef::LitWithUnit(n, ref name) => {
            let number = SnaqNumber::new(n.value_f64(), n.implicit_variance());
            if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(ExprDef::Lit(Quantity::with_number(number, unit)))
            } else {
                Ok(ExprDef::Mul(
                    Box::new(ExprDef::Lit(Quantity::with_number(number, Unit::scalar()))),
                    Box::new(ExprDef::LitSymbol(name.clone())),
                ))
            }
        }
        // Bare identifier: keep as LitSymbol so evaluation can resolve scope-first, then unit, then symbolic.
        // This allows variables to shadow unit names (e.g. DEF=3; DEF+2 works when DEF would otherwise match "da"+"F").
        ExprDef::LitUnit(ref name) => Ok(ExprDef::LitSymbol(name.clone())),
        ExprDef::Lit(_) | ExprDef::LitFuzzyBool(_) | ExprDef::LitSymbol(_) => Ok(def),
        ExprDef::Binding(name, rhs) => {
            let rhs = resolve(*rhs, registry)?;
            Ok(ExprDef::Binding(name, Box::new(rhs)))
        }
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
        ExprDef::Eq(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Eq(Box::new(l), Box::new(r)))
        }
        ExprDef::Ne(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Ne(Box::new(l), Box::new(r)))
        }
        ExprDef::Lt(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Lt(Box::new(l), Box::new(r)))
        }
        ExprDef::Le(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Le(Box::new(l), Box::new(r)))
        }
        ExprDef::Gt(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Gt(Box::new(l), Box::new(r)))
        }
        ExprDef::Ge(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::Ge(Box::new(l), Box::new(r)))
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
        ExprDef::As(expr, unit_expr) => {
            let expr = resolve(*expr, registry)?;
            let unit_expr = resolve_unit_expr(*unit_expr, registry)?;
            Ok(ExprDef::As(Box::new(expr), Box::new(unit_expr)))
        }
        ExprDef::VecLiteral(elems) => {
            let elems = elems
                .into_iter()
                .map(|e| resolve(e, registry))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::VecLiteral(elems))
        }
        ExprDef::Transpose(inner) => {
            let inner = resolve(*inner, registry)?;
            Ok(ExprDef::Transpose(Box::new(inner)))
        }
        ExprDef::Index(base, index) => {
            let base = resolve(*base, registry)?;
            let index = resolve(*index, registry)?;
            Ok(ExprDef::Index(Box::new(base), Box::new(index)))
        }
        ExprDef::Member(base, name) => {
            let base = resolve(*base, registry)?;
            Ok(ExprDef::Member(Box::new(base), name))
        }
        ExprDef::MethodCall(base, name, args) => {
            let base = resolve(*base, registry)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        CallArg::Positional(e) => CallArg::Positional(Box::new(resolve(*e, registry)?)),
                        CallArg::Named(n, e) => CallArg::Named(n, Box::new(resolve(*e, registry)?)),
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::MethodCall(Box::new(base), name, args))
        }
        ExprDef::If(cond, then_b, else_b) => {
            let cond = resolve(*cond, registry)?;
            let then_b = resolve(*then_b, registry)?;
            let else_b = resolve(*else_b, registry)?;
            Ok(ExprDef::If(Box::new(cond), Box::new(then_b), Box::new(else_b)))
        }
        ExprDef::WithPrecision(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(ExprDef::WithPrecision(Box::new(l), Box::new(r)))
        }
        ExprDef::Block(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| resolve(e, registry))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::Block(exprs))
        }
        ExprDef::Lambda(params, body) => {
            let params = params
                .into_iter()
                .map(|(name, default)| {
                    Ok((
                        name,
                        default.map(|d| resolve(*d, registry).map(Box::new)).transpose()?,
                    ))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            let body = resolve(*body, registry)?;
            Ok(ExprDef::Lambda(params, Box::new(body)))
        }
        ExprDef::CallExpr(callee, args) => {
            let callee = resolve(*callee, registry)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        CallArg::Positional(e) => CallArg::Positional(Box::new(resolve(*e, registry)?)),
                        CallArg::Named(n, e) => CallArg::Named(n, Box::new(resolve(*e, registry)?)),
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::CallExpr(Box::new(callee), args))
        }
    }
}

/// Resolve the RHS of "as" (unit-only expression). Only LitUnit, Mul, Div allowed; every ident must be a known unit.
fn resolve_unit_expr(def: ExprDef, registry: &UnitRegistry) -> Result<ExprDef, RunError> {
    match def {
        ExprDef::LitUnit(ref name) => {
            if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(ExprDef::Lit(Quantity::new(1.0, unit)))
            } else {
                Err(RunError::UnknownUnit(name.clone()))
            }
        }
        ExprDef::Mul(l, r) => {
            let l = resolve_unit_expr(*l, registry)?;
            let r = resolve_unit_expr(*r, registry)?;
            Ok(ExprDef::Mul(Box::new(l), Box::new(r)))
        }
        ExprDef::Div(l, r) => {
            let l = resolve_unit_expr(*l, registry)?;
            let r = resolve_unit_expr(*r, registry)?;
            Ok(ExprDef::Div(Box::new(l), Box::new(r)))
        }
        ExprDef::Lit(_) => Ok(def),
        ExprDef::LitFuzzyBool(_)
        | ExprDef::VecLiteral(..)
        | ExprDef::Transpose(..)
        | ExprDef::Index(..)
        | ExprDef::Member(..)
        | ExprDef::MethodCall(..)
        | ExprDef::If(..)
        | ExprDef::Block(..) => Err(RunError::UnknownUnit(
            "as: right side must be a unit or composed units (e.g. m, meters per second)".to_string(),
        )),
        _ => Err(RunError::UnknownUnit(
            "as: right side must be a unit or composed units (e.g. m, meters per second)".to_string(),
        )),
    }
}
