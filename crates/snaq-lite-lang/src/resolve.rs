//! Resolve parsed expression (LitScalar, LitWithUnit, LitUnit, LitTemporal) to Lit(Quantity), LitSymbol, or LitDate.
//! Identifiers that are units resolve to quantities; others resolve to symbols.
//! Preserves source spans through resolution.

use crate::date;
use crate::error::{RunError, RunErrorKind};
use crate::ir::{SpannedCallArg, SpannedExprDef, SpannedExprDefKind};
use crate::quantity::{Quantity, SnaqNumber};
use crate::unit::Unit;
use crate::unit_registry::UnitRegistry;

/// Convert parsed SpannedExprDef (with LitScalar, LitWithUnit, LitUnit) to fully resolved SpannedExprDef (Lit(Quantity), LitSymbol, or compound).
/// Spans are preserved on each node.
pub fn resolve(def: SpannedExprDef, registry: &UnitRegistry) -> Result<SpannedExprDef, RunError> {
    let span = def.span;
    match def.value {
        SpannedExprDefKind::LitScalar(n) => Ok(SpannedExprDef {
            span,
            value: SpannedExprDefKind::Lit(Quantity::with_number(
                SnaqNumber::new(n.value_f64(), n.implicit_variance()),
                Unit::scalar(),
            )),
        }),
        SpannedExprDefKind::LitWithUnit(n, ref name) => {
            let number = SnaqNumber::new(n.value_f64(), n.implicit_variance());
            if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(SpannedExprDef {
                    span,
                    value: SpannedExprDefKind::Lit(Quantity::with_number(number, unit)),
                })
            } else {
                Ok(SpannedExprDef {
                    span,
                    value: SpannedExprDefKind::Mul(
                        Box::new(SpannedExprDef {
                            span,
                            value: SpannedExprDefKind::Lit(Quantity::with_number(
                                number,
                                Unit::scalar(),
                            )),
                        }),
                        Box::new(SpannedExprDef {
                            span,
                            value: SpannedExprDefKind::LitSymbol(name.clone()),
                        }),
                    ),
                })
            }
        }
        SpannedExprDefKind::LitTemporal(ref s) => {
            let gd = date::parse_temporal_literal(s)
                .map_err(|msg| RunError::at(span, RunErrorKind::InvalidTemporalLiteral(msg)))?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::LitDate(gd),
            })
        }
        SpannedExprDefKind::LitDate(gd) => Ok(SpannedExprDef {
            span,
            value: SpannedExprDefKind::LitDate(gd),
        }),
        SpannedExprDefKind::LitUnit(ref name) => Ok(SpannedExprDef {
            span,
            value: SpannedExprDefKind::LitSymbol(name.clone()),
        }),
        SpannedExprDefKind::Lit(_)
        | SpannedExprDefKind::LitFuzzyBool(_)
        | SpannedExprDefKind::LitSymbol(_) => Ok(SpannedExprDef { span, value: def.value }),
        SpannedExprDefKind::Binding(name, rhs) => {
            let rhs = resolve(*rhs, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Binding(name, Box::new(rhs)),
            })
        }
        SpannedExprDefKind::Add(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Add(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Sub(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Sub(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Mul(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Mul(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Div(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Div(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Eq(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Eq(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Ne(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Ne(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Lt(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Lt(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Le(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Le(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Gt(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Gt(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Ge(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Ge(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::And(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::And(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Neg(inner) => {
            let inner = resolve(*inner, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Neg(Box::new(inner)),
            })
        }
        SpannedExprDefKind::Call(name, args) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok::<SpannedCallArg, RunError>(match arg {
                        SpannedCallArg::Positional(e) => {
                            SpannedCallArg::Positional(Box::new(resolve(*e, registry)?))
                        }
                        SpannedCallArg::Named(n, e) => {
                            SpannedCallArg::Named(n, Box::new(resolve(*e, registry)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Call(name, args),
            })
        }
        SpannedExprDefKind::As(expr, unit_expr) => {
            let expr = resolve(*expr, registry)?;
            let unit_expr = resolve_unit_expr(*unit_expr, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::As(Box::new(expr), Box::new(unit_expr)),
            })
        }
        SpannedExprDefKind::VecLiteral(elems) => {
            let elems = elems
                .into_iter()
                .map(|e| resolve(e, registry))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::VecLiteral(elems),
            })
        }
        SpannedExprDefKind::MapLiteral(entries) => {
            let entries = entries
                .into_iter()
                .map(|(k, v)| Ok((k, resolve(v, registry)?)))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::MapLiteral(entries),
            })
        }
        SpannedExprDefKind::Transpose(inner) => {
            let inner = resolve(*inner, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Transpose(Box::new(inner)),
            })
        }
        SpannedExprDefKind::Index(base, key) => {
            let base = resolve(*base, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Index(Box::new(base), key),
            })
        }
        SpannedExprDefKind::Member(base, name) => {
            let base = resolve(*base, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Member(Box::new(base), name),
            })
        }
        SpannedExprDefKind::MethodCall(base, name, args) => {
            let base = resolve(*base, registry)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        SpannedCallArg::Positional(e) => {
                            SpannedCallArg::Positional(Box::new(resolve(*e, registry)?))
                        }
                        SpannedCallArg::Named(n, e) => {
                            SpannedCallArg::Named(n, Box::new(resolve(*e, registry)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::MethodCall(Box::new(base), name, args),
            })
        }
        SpannedExprDefKind::If(cond, then_b, else_b) => {
            let cond = resolve(*cond, registry)?;
            let then_b = resolve(*then_b, registry)?;
            let else_b = resolve(*else_b, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::If(
                    Box::new(cond),
                    Box::new(then_b),
                    Box::new(else_b),
                ),
            })
        }
        SpannedExprDefKind::WithPrecision(l, r) => {
            let l = resolve(*l, registry)?;
            let r = resolve(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::WithPrecision(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Block(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| resolve(e, registry))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Block(exprs),
            })
        }
        SpannedExprDefKind::Lambda(params, body) => {
            let params = params
                .into_iter()
                .map(|(name, default)| {
                    Ok((
                        name,
                        default
                            .map(|d| resolve(*d, registry).map(Box::new))
                            .transpose()?,
                    ))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            let body = resolve(*body, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Lambda(params, Box::new(body)),
            })
        }
        SpannedExprDefKind::CallExpr(callee, args) => {
            let callee = resolve(*callee, registry)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        SpannedCallArg::Positional(e) => {
                            SpannedCallArg::Positional(Box::new(resolve(*e, registry)?))
                        }
                        SpannedCallArg::Named(n, e) => {
                            SpannedCallArg::Named(n, Box::new(resolve(*e, registry)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::CallExpr(Box::new(callee), args),
            })
        }
    }
}

/// Resolve the RHS of "as" (unit-only expression). Only LitUnit, Mul, Div allowed; every ident must be a known unit.
fn resolve_unit_expr(
    def: SpannedExprDef,
    registry: &UnitRegistry,
) -> Result<SpannedExprDef, RunError> {
    let span = def.span;
    match def.value {
        SpannedExprDefKind::LitUnit(ref name) => {
            if let Some(unit) = registry.get_unit_with_prefix(name) {
                Ok(SpannedExprDef {
                    span,
                    value: SpannedExprDefKind::Lit(Quantity::new(1.0, unit)),
                })
            } else {
                Err(RunError::at(span, RunErrorKind::UnknownUnit(name.clone())))
            }
        }
        SpannedExprDefKind::Mul(l, r) => {
            let l = resolve_unit_expr(*l, registry)?;
            let r = resolve_unit_expr(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Mul(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Div(l, r) => {
            let l = resolve_unit_expr(*l, registry)?;
            let r = resolve_unit_expr(*r, registry)?;
            Ok(SpannedExprDef {
                span,
                value: SpannedExprDefKind::Div(Box::new(l), Box::new(r)),
            })
        }
        SpannedExprDefKind::Lit(_) => Ok(SpannedExprDef { span, value: def.value }),
        SpannedExprDefKind::LitFuzzyBool(_)
        | SpannedExprDefKind::VecLiteral(..)
        | SpannedExprDefKind::Transpose(..)
        | SpannedExprDefKind::Index(..)
        | SpannedExprDefKind::Member(..)
        | SpannedExprDefKind::MethodCall(..)
        | SpannedExprDefKind::If(..)
        | SpannedExprDefKind::Block(..)
        | SpannedExprDefKind::MapLiteral(..) => Err(RunError::at(span, RunErrorKind::UnknownUnit(
            "as: right side must be a unit or composed units (e.g. m, meters per second)"
                .to_string(),
        ))),
        _ => Err(RunError::at(span, RunErrorKind::UnknownUnit(
            "as: right side must be a unit or composed units (e.g. m, meters per second)"
                .to_string(),
        ))),
    }
}
