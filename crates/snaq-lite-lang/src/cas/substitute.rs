//! Substitute symbols with numeric values at AST level.

use crate::error::RunError;
use crate::ir::ExprDef;
use crate::quantity::Quantity;
use crate::symbol_registry::SymbolRegistry;

/// Replace every LitSymbol(name) with Lit(Quantity::from_scalar(value)) using the registry.
/// Returns RunError::SymbolHasNoValue(name) if any symbol has no value.
pub fn substitute_symbols(def: ExprDef, registry: &SymbolRegistry) -> Result<ExprDef, RunError> {
    match def {
        ExprDef::Lit(q) => Ok(ExprDef::Lit(q)),
        ExprDef::LitFuzzyBool(f) => Ok(ExprDef::LitFuzzyBool(f)),
        ExprDef::LitSymbol(name) => {
            let value = registry.get(&name).ok_or(RunError::SymbolHasNoValue(name))?;
            Ok(ExprDef::Lit(Quantity::from_scalar(value)))
        }
        ExprDef::Add(l, r) => Ok(ExprDef::Add(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Sub(l, r) => Ok(ExprDef::Sub(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Mul(l, r) => Ok(ExprDef::Mul(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Div(l, r) => Ok(ExprDef::Div(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Neg(inner) => Ok(ExprDef::Neg(Box::new(substitute_symbols(*inner, registry)?))),
        ExprDef::Call(name, args) => {
            let args = args
                .into_iter()
                .map(|arg| {
                    Ok::<crate::ir::CallArg, RunError>(match arg {
                        crate::ir::CallArg::Positional(e) => {
                            crate::ir::CallArg::Positional(Box::new(substitute_symbols(*e, registry)?))
                        }
                        crate::ir::CallArg::Named(n, e) => {
                            crate::ir::CallArg::Named(n, Box::new(substitute_symbols(*e, registry)?))
                        }
                    })
                })
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::Call(name, args))
        }
        ExprDef::As(l, r) => Ok(ExprDef::As(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::VecLiteral(elems) => {
            let elems = elems
                .into_iter()
                .map(|e| substitute_symbols(e, registry))
                .collect::<Result<Vec<_>, RunError>>()?;
            Ok(ExprDef::VecLiteral(elems))
        }
        ExprDef::Transpose(inner) => Ok(ExprDef::Transpose(Box::new(substitute_symbols(*inner, registry)?))),
        ExprDef::Eq(l, r) => Ok(ExprDef::Eq(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Ne(l, r) => Ok(ExprDef::Ne(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Lt(l, r) => Ok(ExprDef::Lt(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Le(l, r) => Ok(ExprDef::Le(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Gt(l, r) => Ok(ExprDef::Gt(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::Ge(l, r) => Ok(ExprDef::Ge(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::If(cond, then_b, else_b) => Ok(ExprDef::If(
            Box::new(substitute_symbols(*cond, registry)?),
            Box::new(substitute_symbols(*then_b, registry)?),
            Box::new(substitute_symbols(*else_b, registry)?),
        )),
        ExprDef::WithPrecision(l, r) => Ok(ExprDef::WithPrecision(
            Box::new(substitute_symbols(*l, registry)?),
            Box::new(substitute_symbols(*r, registry)?),
        )),
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved ExprDef: resolve() must be called before substitute_symbols")
        }
    }
}
