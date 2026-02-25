//! Computer Algebra System: interning, canonicalization, and term rewriting.
//!
//! All transformations are pure: input AST → output AST. The CAS uses an
//! interned representation (ExprId into a pool) so structural equality is O(1).

mod canonical;
mod convert;
mod interner;
mod rewrite;
mod substitute;

pub use canonical::{canonicalize, rank, Rank};
pub use convert::{
    expr_def_to_interned, interned_to_expr_def, interned_to_spanned_expr_def,
    spanned_expr_def_to_interned,
};
pub use interner::{ExprId, ExprInterner, ExprNode};
pub use rewrite::rewrite;
pub use substitute::{substitute_symbols, substitute_symbols_spanned};

use crate::error::RunError;
use crate::ir::SpannedExprDef;
use crate::symbol_registry::SymbolRegistry;
use crate::unit_registry::UnitRegistry;

/// Symbolic mode: canonicalize and rewrite; symbols remain. Returns simplified SpannedExprDef.
/// Can return RunError::DivisionByZero if a numeric subexpression divides by zero.
pub fn simplify_symbolic(
    def: SpannedExprDef,
    registry: &UnitRegistry,
) -> Result<SpannedExprDef, RunError> {
    let mut pool = ExprInterner::new();
    let id = spanned_expr_def_to_interned(&def, &mut pool);
    let (cpool, croot) = canonicalize(&pool, id);
    let (rpool, rroot) = rewrite(&cpool, croot, registry)?;
    Ok(interned_to_spanned_expr_def(&rpool, rroot))
}

/// Numeric mode: substitute symbols then canonicalize and rewrite. Constant folding collapses to numeric result.
pub fn simplify_numeric(
    def: SpannedExprDef,
    unit_registry: &UnitRegistry,
    symbol_registry: &SymbolRegistry,
) -> Result<SpannedExprDef, RunError> {
    let def = substitute_symbols_spanned(def, symbol_registry, unit_registry)?;
    let mut pool = ExprInterner::new();
    let id = spanned_expr_def_to_interned(&def, &mut pool);
    let (cpool, croot) = canonicalize(&pool, id);
    let (rpool, rroot) = rewrite(&cpool, croot, unit_registry)?;
    Ok(interned_to_spanned_expr_def(&rpool, rroot))
}
