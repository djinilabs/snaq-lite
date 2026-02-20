//! IR: inputs and tracked expression graph for the reactive computation.

use crate::quantity::Quantity;
use ordered_float::OrderedFloat;

/// Definition of the root expression (plain data, no Salsa).
/// Parser produces LitScalar, LitWithUnit, LitUnit; after resolve() only Lit(Quantity) | LitSymbol | Add | Sub | Mul | Div remain.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExprDef {
    /// Parsed: bare number (scalar).
    LitScalar(OrderedFloat<f64>),
    /// Parsed: number and unit identifier (e.g. "100 m").
    LitWithUnit(OrderedFloat<f64>, String),
    /// Parsed: unit only (e.g. "hour" = 1 hour).
    LitUnit(String),
    /// Resolved: quantity (value + unit).
    Lit(Quantity),
    /// Resolved: bare symbol (e.g. pi, e). Identifier not found in unit registry.
    LitSymbol(String),
    Add(Box<ExprDef>, Box<ExprDef>),
    Sub(Box<ExprDef>, Box<ExprDef>),
    Mul(Box<ExprDef>, Box<ExprDef>),
    Div(Box<ExprDef>, Box<ExprDef>),
    /// Unary minus (e.g. "-1", "-(2 * 3)").
    Neg(Box<ExprDef>),
}

/// Input that holds the root expression definition.
#[salsa::input]
pub struct ProgramDef {
    #[returns(ref)]
    pub root: ExprDef,
}

/// A single expression node in the computation graph (tracked by Salsa).
#[salsa::tracked(debug)]
pub struct Expression<'db> {
    #[returns(ref)]
    pub data: ExprData<'db>,
}

/// Data for an expression node; can reference other expressions.
#[derive(Clone, PartialEq, Eq, Hash, Debug, salsa::Update)]
pub enum ExprData<'db> {
    Lit(Quantity),
    LitSymbol(String),
    Add(Expression<'db>, Expression<'db>),
    Sub(Expression<'db>, Expression<'db>),
    Mul(Expression<'db>, Expression<'db>),
    Div(Expression<'db>, Expression<'db>),
    Neg(Expression<'db>),
}
