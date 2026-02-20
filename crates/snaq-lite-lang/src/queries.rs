//! Query group: build expression graph and evaluate.
//!
//! When inputs (`Numbers` or `ProgramDef`) change, Salsa invalidates only the memoized
//! results that depended on them, so recomputation is incremental.

use crate::ir::{ExprData, ExprDef, Expression, Numbers, ProgramDef};

/// Build the tracked expression graph from the program definition; returns the root.
#[salsa::tracked]
pub fn program(db: &dyn salsa::Database, program_def: ProgramDef) -> Expression<'_> {
    let root_def = program_def.root(db);
    build_expression(db, root_def.clone())
}

/// Recursively build tracked Expression nodes from ExprDef.
fn build_expression(db: &dyn salsa::Database, def: ExprDef) -> Expression<'_> {
    let data = match def {
        ExprDef::LitA => ExprData::LitA,
        ExprDef::LitB => ExprData::LitB,
        ExprDef::Add(l, r) => {
            let left = build_expression(db, *l);
            let right = build_expression(db, *r);
            ExprData::Add(left, right)
        }
        ExprDef::Sub(l, r) => {
            let left = build_expression(db, *l);
            let right = build_expression(db, *r);
            ExprData::Sub(left, right)
        }
    };
    Expression::new(db, data)
}

/// Evaluate an expression to its numeric value.
///
/// Memoized per `(numbers, expr)`; when `numbers` or any child's value changes,
/// only dependent entries are recomputed.
#[salsa::tracked]
pub fn value(db: &dyn salsa::Database, numbers: Numbers, expr: Expression<'_>) -> i64 {
    let data = expr.data(db);
    match data {
        ExprData::LitA => numbers.a(db),
        ExprData::LitB => numbers.b(db),
        ExprData::Add(l, r) => value(db, numbers, *l) + value(db, numbers, *r),
        ExprData::Sub(l, r) => value(db, numbers, *l) - value(db, numbers, *r),
    }
}
