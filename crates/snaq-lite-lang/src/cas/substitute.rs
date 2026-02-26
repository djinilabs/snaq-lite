//! Substitute symbols with numeric values at AST level.
//!
//! Names that appear in a binding anywhere in the tree are left as `LitSymbol` so that
//! [run_numeric](crate::run_numeric) evaluation can resolve them from scope (variables shadow units).

use std::collections::HashSet;

use crate::error::{RunError, RunErrorKind};
use crate::ir::{ExprDef, SpannedCallArg, SpannedExprDef, SpannedExprDefKind};
use crate::quantity::Quantity;
use crate::symbol_registry::SymbolRegistry;
use crate::unit_registry::UnitRegistry;

/// Collect every name that appears as a binding in the tree (so we leave them as LitSymbol for value() to resolve from scope).
fn collect_bound_names(def: &ExprDef) -> HashSet<String> {
    let mut names = HashSet::new();
    fn go(def: &ExprDef, names: &mut HashSet<String>) {
        match def {
            ExprDef::Binding(name, rhs) => {
                names.insert(name.clone());
                go(rhs, names);
            }
            ExprDef::Block(exprs) => {
                for e in exprs {
                    go(e, names);
                }
            }
            ExprDef::Add(l, r) | ExprDef::Sub(l, r) | ExprDef::Mul(l, r) | ExprDef::Div(l, r)
            | ExprDef::Eq(l, r) | ExprDef::Ne(l, r) | ExprDef::Lt(l, r) | ExprDef::Le(l, r)
            | ExprDef::Gt(l, r) | ExprDef::Ge(l, r) | ExprDef::And(l, r) | ExprDef::As(l, r) | ExprDef::WithPrecision(l, r) => {
                go(l, names);
                go(r, names);
            }
            ExprDef::Neg(inner) | ExprDef::Transpose(inner) => go(inner, names),
            ExprDef::Index(base, _key) => go(base, names),
            ExprDef::Member(base, _) => go(base, names),
            ExprDef::MethodCall(base, _, args) => {
                go(base, names);
                for arg in args {
                    match arg {
                        crate::ir::CallArg::Positional(e) | crate::ir::CallArg::Named(_, e) => go(e, names),
                    }
                }
            }
            ExprDef::If(cond, then_b, else_b) => {
                go(cond, names);
                go(then_b, names);
                go(else_b, names);
            }
            ExprDef::Call(_, args) => {
                for arg in args {
                    match arg {
                        crate::ir::CallArg::Positional(e) | crate::ir::CallArg::Named(_, e) => go(e, names),
                    }
                }
            }
            ExprDef::Lambda(params, body) => {
                for (name, default) in params {
                    names.insert(name.clone());
                    if let Some(d) = default {
                        go(d, names);
                    }
                }
                go(body, names);
            }
            ExprDef::CallExpr(callee, args) => {
                go(callee, names);
                for arg in args {
                    match arg {
                        crate::ir::CallArg::Positional(e) | crate::ir::CallArg::Named(_, e) => go(e, names),
                    }
                }
            }
            ExprDef::VecLiteral(elems) => {
                for e in elems {
                    go(e, names);
                }
            }
            ExprDef::MapLiteral(entries) => {
                for (_, v) in entries {
                    go(v, names);
                }
            }
            ExprDef::Lit(_) | ExprDef::LitFuzzyBool(_) | ExprDef::LitSymbol(_)
            | ExprDef::LitTemporal(_) | ExprDef::LitDate(_) | ExprDef::ExternalStream(_)
            | ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {}
        }
    }
    go(def, &mut names);
    names
}

/// Replace every LitSymbol(name) with Lit(Quantity): from symbol registry (scalar) or unit registry (1 in that unit).
/// Names that are bound in the program (appear in some Binding) are left as LitSymbol so value() resolves them from scope.
/// Returns RunError::SymbolHasNoValue(name) if the name is in neither registry and not bound.
pub fn substitute_symbols(
    def: ExprDef,
    symbol_registry: &SymbolRegistry,
    unit_registry: &UnitRegistry,
) -> Result<ExprDef, RunError> {
    let bound_names = collect_bound_names(&def);
    substitute_symbols_inner(def, symbol_registry, unit_registry, &bound_names)
}

/// Collect bound names from a SpannedExprDef (for substitute_symbols_spanned).
fn collect_bound_names_spanned(def: &SpannedExprDef) -> HashSet<String> {
    let mut names = HashSet::new();
    fn go(def: &SpannedExprDef, names: &mut HashSet<String>) {
        match &def.value {
            SpannedExprDefKind::Binding(name, rhs) => {
                names.insert(name.clone());
                go(rhs, names);
            }
            SpannedExprDefKind::Block(exprs) => {
                for e in exprs {
                    go(e, names);
                }
            }
            SpannedExprDefKind::Add(l, r) | SpannedExprDefKind::Sub(l, r) | SpannedExprDefKind::Mul(l, r)
            | SpannedExprDefKind::Div(l, r) | SpannedExprDefKind::Eq(l, r) | SpannedExprDefKind::Ne(l, r)
            | SpannedExprDefKind::Lt(l, r) | SpannedExprDefKind::Le(l, r) | SpannedExprDefKind::Gt(l, r)
            | SpannedExprDefKind::Ge(l, r) | SpannedExprDefKind::And(l, r) | SpannedExprDefKind::As(l, r)
            | SpannedExprDefKind::WithPrecision(l, r) => {
                go(l, names);
                go(r, names);
            }
            SpannedExprDefKind::Neg(inner) | SpannedExprDefKind::Transpose(inner) => go(inner, names),
            SpannedExprDefKind::Index(base, _key) => go(base, names),
            SpannedExprDefKind::Member(base, _) => go(base, names),
            SpannedExprDefKind::MethodCall(base, _, args) => {
                go(base, names);
                for arg in args {
                    match arg {
                        SpannedCallArg::Positional(e) | SpannedCallArg::Named(_, e) => go(e, names),
                    }
                }
            }
            SpannedExprDefKind::If(cond, then_b, else_b) => {
                go(cond, names);
                go(then_b, names);
                go(else_b, names);
            }
            SpannedExprDefKind::Call(_, args) => {
                for arg in args {
                    match arg {
                        SpannedCallArg::Positional(e) | SpannedCallArg::Named(_, e) => go(e, names),
                    }
                }
            }
            SpannedExprDefKind::Lambda(params, body) => {
                for (name, default) in params {
                    names.insert(name.clone());
                    if let Some(d) = default {
                        go(d, names);
                    }
                }
                go(body, names);
            }
            SpannedExprDefKind::CallExpr(callee, args) => {
                go(callee, names);
                for arg in args {
                    match arg {
                        SpannedCallArg::Positional(e) | SpannedCallArg::Named(_, e) => go(e, names),
                    }
                }
            }
            SpannedExprDefKind::VecLiteral(elems) => {
                for e in elems {
                    go(e, names);
                }
            }
            SpannedExprDefKind::MapLiteral(entries) => {
                for (_, v) in entries {
                    go(v, names);
                }
            }
            SpannedExprDefKind::Lit(_) | SpannedExprDefKind::LitFuzzyBool(_) | SpannedExprDefKind::LitSymbol(_)
            | SpannedExprDefKind::LitTemporal(_) | SpannedExprDefKind::LitDate(_)
            | SpannedExprDefKind::ExternalStream(_)
            | SpannedExprDefKind::LitScalar(..) | SpannedExprDefKind::LitWithUnit(..)
            | SpannedExprDefKind::LitUnit(..) => {}
        }
    }
    go(def, &mut names);
    names
}

/// Spanned version: substitute symbols and preserve source spans.
pub fn substitute_symbols_spanned(
    def: SpannedExprDef,
    symbol_registry: &SymbolRegistry,
    unit_registry: &UnitRegistry,
) -> Result<SpannedExprDef, RunError> {
    let bound_names = collect_bound_names_spanned(&def);
    substitute_symbols_spanned_inner(def, symbol_registry, unit_registry, &bound_names)
}

fn substitute_symbols_spanned_inner(
    def: SpannedExprDef,
    symbol_registry: &SymbolRegistry,
    unit_registry: &UnitRegistry,
    bound_names: &HashSet<String>,
) -> Result<SpannedExprDef, RunError> {
    let span = def.span;
    let value = match def.value {
        SpannedExprDefKind::Lit(q) => SpannedExprDefKind::Lit(q),
        SpannedExprDefKind::LitFuzzyBool(f) => SpannedExprDefKind::LitFuzzyBool(f),
        SpannedExprDefKind::LitDate(gd) => SpannedExprDefKind::LitDate(gd),
        SpannedExprDefKind::ExternalStream(name) => SpannedExprDefKind::ExternalStream(name),
        SpannedExprDefKind::LitTemporal(_) => {
            return Err(RunError::at(span, RunErrorKind::InvalidTemporalLiteral(
                "unresolved temporal literal (resolve must run before substitute)".to_string(),
            )));
        }
        SpannedExprDefKind::LitSymbol(name) => {
            if bound_names.contains(&name) {
                SpannedExprDefKind::LitSymbol(name)
            } else if let Some(value) = symbol_registry.get(&name) {
                SpannedExprDefKind::Lit(Quantity::from_scalar(value))
            } else if let Some(unit) = unit_registry.get_unit_with_prefix(&name) {
                SpannedExprDefKind::Lit(Quantity::new(1.0, unit))
            } else {
                return Err(RunError::at(span, RunErrorKind::SymbolHasNoValue(name)));
            }
        }
        SpannedExprDefKind::Add(l, r) => SpannedExprDefKind::Add(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Sub(l, r) => SpannedExprDefKind::Sub(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Mul(l, r) => SpannedExprDefKind::Mul(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Div(l, r) => SpannedExprDefKind::Div(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Neg(inner) => {
            SpannedExprDefKind::Neg(Box::new(substitute_symbols_spanned_inner(*inner, symbol_registry, unit_registry, bound_names)?))
        }
        SpannedExprDefKind::Call(name, args) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok::<SpannedCallArg, RunError>(match arg {
                        SpannedCallArg::Positional(e) => {
                            SpannedCallArg::Positional(Box::new(substitute_symbols_spanned_inner(*e, symbol_registry, unit_registry, bound_names)?))
                        }
                        SpannedCallArg::Named(n, e) => {
                            SpannedCallArg::Named(n, Box::new(substitute_symbols_spanned_inner(*e, symbol_registry, unit_registry, bound_names)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            SpannedExprDefKind::Call(name, args)
        }
        SpannedExprDefKind::As(l, r) => SpannedExprDefKind::As(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::VecLiteral(elems) => {
            let elems = elems
                .into_iter()
                .map(|e| substitute_symbols_spanned_inner(e, symbol_registry, unit_registry, bound_names))
                .collect::<Result<Vec<_>, RunError>>()?;
            SpannedExprDefKind::VecLiteral(elems)
        }
        SpannedExprDefKind::Transpose(inner) => {
            SpannedExprDefKind::Transpose(Box::new(substitute_symbols_spanned_inner(*inner, symbol_registry, unit_registry, bound_names)?))
        }
        SpannedExprDefKind::Index(base, key) => SpannedExprDefKind::Index(
            Box::new(substitute_symbols_spanned_inner(*base, symbol_registry, unit_registry, bound_names)?),
            key,
        ),
        SpannedExprDefKind::Member(base, name) => SpannedExprDefKind::Member(
            Box::new(substitute_symbols_spanned_inner(*base, symbol_registry, unit_registry, bound_names)?),
            name,
        ),
        SpannedExprDefKind::MethodCall(base, name, args) => {
            let args: Vec<SpannedCallArg> = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        SpannedCallArg::Positional(e) => {
                            SpannedCallArg::Positional(Box::new(substitute_symbols_spanned_inner(
                                *e, symbol_registry, unit_registry, bound_names,
                            )?))
                        }
                        SpannedCallArg::Named(n, e) => {
                            SpannedCallArg::Named(
                                n,
                                Box::new(substitute_symbols_spanned_inner(
                                    *e, symbol_registry, unit_registry, bound_names,
                                )?),
                            )
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            SpannedExprDefKind::MethodCall(
                Box::new(substitute_symbols_spanned_inner(*base, symbol_registry, unit_registry, bound_names)?),
                name,
                args,
            )
        }
        SpannedExprDefKind::Eq(l, r) => SpannedExprDefKind::Eq(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Ne(l, r) => SpannedExprDefKind::Ne(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Lt(l, r) => SpannedExprDefKind::Lt(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Le(l, r) => SpannedExprDefKind::Le(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Gt(l, r) => SpannedExprDefKind::Gt(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Ge(l, r) => SpannedExprDefKind::Ge(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::And(l, r) => SpannedExprDefKind::And(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::If(cond, then_b, else_b) => SpannedExprDefKind::If(
            Box::new(substitute_symbols_spanned_inner(*cond, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*then_b, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*else_b, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::WithPrecision(l, r) => SpannedExprDefKind::WithPrecision(
            Box::new(substitute_symbols_spanned_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_spanned_inner(*r, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Binding(name, rhs) => SpannedExprDefKind::Binding(
            name,
            Box::new(substitute_symbols_spanned_inner(*rhs, symbol_registry, unit_registry, bound_names)?),
        ),
        SpannedExprDefKind::Block(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| substitute_symbols_spanned_inner(e, symbol_registry, unit_registry, bound_names))
                .collect::<Result<Vec<_>, RunError>>()?;
            SpannedExprDefKind::Block(exprs)
        }
        SpannedExprDefKind::MapLiteral(entries) => {
            let entries = entries
                .into_iter()
                .map(|(k, v)| {
                    Ok((k, substitute_symbols_spanned_inner(v, symbol_registry, unit_registry, bound_names)?))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            SpannedExprDefKind::MapLiteral(entries)
        }
        SpannedExprDefKind::Lambda(params, body) => {
            let mut lambda_bound = bound_names.clone();
            for (name, _) in &params {
                lambda_bound.insert(name.clone());
            }
            let params = params
                .into_iter()
                .map(|(name, default)| {
                    Ok((
                        name,
                        default
                            .map(|d| {
                                substitute_symbols_spanned_inner(*d, symbol_registry, unit_registry, &lambda_bound)
                                    .map(Box::new)
                            })
                            .transpose()?,
                    ))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            let body = substitute_symbols_spanned_inner(*body, symbol_registry, unit_registry, &lambda_bound)?;
            SpannedExprDefKind::Lambda(params, Box::new(body))
        }
        SpannedExprDefKind::CallExpr(callee, args) => {
            let callee = substitute_symbols_spanned_inner(*callee, symbol_registry, unit_registry, bound_names)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        SpannedCallArg::Positional(e) => {
                            SpannedCallArg::Positional(Box::new(substitute_symbols_spanned_inner(
                                *e, symbol_registry, unit_registry, bound_names,
                            )?))
                        }
                        SpannedCallArg::Named(n, e) => {
                            SpannedCallArg::Named(
                                n,
                                Box::new(substitute_symbols_spanned_inner(
                                    *e, symbol_registry, unit_registry, bound_names,
                                )?),
                            )
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            SpannedExprDefKind::CallExpr(Box::new(callee), args)
        }
        SpannedExprDefKind::LitScalar(..) | SpannedExprDefKind::LitWithUnit(..) | SpannedExprDefKind::LitUnit(..) => {
            panic!("unresolved SpannedExprDef: resolve() must be called before substitute_symbols_spanned")
        }
    };
    Ok(SpannedExprDef { span, value })
}

fn substitute_symbols_inner(
    def: ExprDef,
    symbol_registry: &SymbolRegistry,
    unit_registry: &UnitRegistry,
    bound_names: &HashSet<String>,
) -> Result<ExprDef, RunError> {
    match def {
        ExprDef::Lit(q) => Ok(ExprDef::Lit(q)),
        ExprDef::LitFuzzyBool(f) => Ok(ExprDef::LitFuzzyBool(f)),
        ExprDef::LitDate(gd) => Ok(ExprDef::LitDate(gd)),
        ExprDef::ExternalStream(name) => Ok(ExprDef::ExternalStream(name)),
        ExprDef::LitTemporal(_) => panic!("unresolved LitTemporal: resolve() must be called before substitute_symbols"),
        ExprDef::LitSymbol(name) => {
            if bound_names.contains(&name) {
                Ok(ExprDef::LitSymbol(name))
            } else if let Some(value) = symbol_registry.get(&name) {
                Ok(ExprDef::Lit(Quantity::from_scalar(value)))
            } else if let Some(unit) = unit_registry.get_unit_with_prefix(&name) {
                Ok(ExprDef::Lit(Quantity::new(1.0, unit)))
            } else {
                Err(RunError::new(RunErrorKind::SymbolHasNoValue(name)))
            }
        }
        ExprDef::Add(l, r) => Ok(ExprDef::Add(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Sub(l, r) => Ok(ExprDef::Sub(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Mul(l, r) => Ok(ExprDef::Mul(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Div(l, r) => Ok(ExprDef::Div(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Neg(inner) => Ok(ExprDef::Neg(Box::new(substitute_symbols_inner(*inner, symbol_registry, unit_registry, bound_names)?))),
        ExprDef::Call(name, args) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok::<crate::ir::CallArg, RunError>(match arg {
                        crate::ir::CallArg::Positional(e) => {
                            crate::ir::CallArg::Positional(Box::new(substitute_symbols_inner(*e, symbol_registry, unit_registry, bound_names)?))
                        }
                        crate::ir::CallArg::Named(n, e) => {
                            crate::ir::CallArg::Named(n, Box::new(substitute_symbols_inner(*e, symbol_registry, unit_registry, bound_names)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::Call(name, args))
        }
        ExprDef::As(l, r) => Ok(ExprDef::As(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::VecLiteral(elems) => {
            let elems = elems
                .into_iter()
                .map(|e| substitute_symbols_inner(e, symbol_registry, unit_registry, bound_names))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::VecLiteral(elems))
        }
        ExprDef::MapLiteral(entries) => {
            let entries = entries
                .into_iter()
                .map(|(k, v)| {
                    Ok((
                        k,
                        Box::new(substitute_symbols_inner(*v, symbol_registry, unit_registry, bound_names)?),
                    ))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::MapLiteral(entries))
        }
        ExprDef::Transpose(inner) => Ok(ExprDef::Transpose(Box::new(substitute_symbols_inner(*inner, symbol_registry, unit_registry, bound_names)?))),
        ExprDef::Index(base, key) => Ok(ExprDef::Index(
            Box::new(substitute_symbols_inner(*base, symbol_registry, unit_registry, bound_names)?),
            key,
        )),
        ExprDef::Member(base, name) => Ok(ExprDef::Member(
            Box::new(substitute_symbols_inner(*base, symbol_registry, unit_registry, bound_names)?),
            name,
        )),
        ExprDef::MethodCall(base, name, args) => {
            let args: Vec<crate::ir::CallArg> = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        crate::ir::CallArg::Positional(e) => {
                            crate::ir::CallArg::Positional(Box::new(
                                substitute_symbols_inner(*e, symbol_registry, unit_registry, bound_names)?,
                            ))
                        }
                        crate::ir::CallArg::Named(n, e) => {
                            crate::ir::CallArg::Named(
                                n,
                                Box::new(substitute_symbols_inner(
                                    *e, symbol_registry, unit_registry, bound_names,
                                )?),
                            )
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::MethodCall(
                Box::new(substitute_symbols_inner(*base, symbol_registry, unit_registry, bound_names)?),
                name,
                args,
            ))
        }
        ExprDef::Eq(l, r) => Ok(ExprDef::Eq(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Ne(l, r) => Ok(ExprDef::Ne(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Lt(l, r) => Ok(ExprDef::Lt(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Le(l, r) => Ok(ExprDef::Le(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Gt(l, r) => Ok(ExprDef::Gt(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Ge(l, r) => Ok(ExprDef::Ge(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::And(l, r) => Ok(ExprDef::And(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::If(cond, then_b, else_b) => Ok(ExprDef::If(
            Box::new(substitute_symbols_inner(*cond, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*then_b, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*else_b, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::WithPrecision(l, r) => Ok(ExprDef::WithPrecision(
            Box::new(substitute_symbols_inner(*l, symbol_registry, unit_registry, bound_names)?),
            Box::new(substitute_symbols_inner(*r, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Binding(name, rhs) => Ok(ExprDef::Binding(
            name,
            Box::new(substitute_symbols_inner(*rhs, symbol_registry, unit_registry, bound_names)?),
        )),
        ExprDef::Block(exprs) => {
            let exprs = exprs
                .into_iter()
                .map(|e| substitute_symbols_inner(e, symbol_registry, unit_registry, bound_names))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::Block(exprs))
        }
        ExprDef::Lambda(params, body) => {
            let mut lambda_bound = bound_names.clone();
            for (name, _) in &params {
                lambda_bound.insert(name.clone());
            }
            let params = params
                .into_iter()
                .map(|(name, default)| {
                    Ok((
                        name,
                        default
                            .map(|d| substitute_symbols_inner(*d, symbol_registry, unit_registry, &lambda_bound).map(Box::new))
                            .transpose()?,
                    ))
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            let body = substitute_symbols_inner(*body, symbol_registry, unit_registry, &lambda_bound)?;
            Ok(ExprDef::Lambda(params, Box::new(body)))
        }
        ExprDef::CallExpr(callee, args) => {
            let callee = substitute_symbols_inner(*callee, symbol_registry, unit_registry, bound_names)?;
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok(match arg {
                        crate::ir::CallArg::Positional(e) => {
                            crate::ir::CallArg::Positional(Box::new(substitute_symbols_inner(*e, symbol_registry, unit_registry, bound_names)?))
                        }
                        crate::ir::CallArg::Named(n, e) => {
                            crate::ir::CallArg::Named(n, Box::new(substitute_symbols_inner(*e, symbol_registry, unit_registry, bound_names)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::CallExpr(Box::new(callee), args))
        }
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved ExprDef: resolve() must be called before substitute_symbols")
        }
    }
}

