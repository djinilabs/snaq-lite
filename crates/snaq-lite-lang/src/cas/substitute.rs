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
        ExprDef::LitScalar(..) | ExprDef::LitWithUnit(..) | ExprDef::LitUnit(..) => {
            panic!("unresolved ExprDef: resolve() must be called before substitute_symbols")
        }
    }
}
