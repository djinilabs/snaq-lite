//! IR: inputs and tracked expression graph for the reactive computation.

use crate::fuzzy::FuzzyBool;
use crate::quantity::Quantity;
use ordered_float::OrderedFloat;

/// A single argument in a function call: either positional or named.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum CallArg {
    /// Positional argument (e.g. `1` in `max(1, 2)`).
    Positional(Box<ExprDef>),
    /// Named argument (e.g. `b: 2` in `max(a: 1, b: 2)`).
    Named(String, Box<ExprDef>),
}

/// Definition of the root expression (plain data, no Salsa).
/// Parser produces LitScalar, LitWithUnit, LitUnit, Call; after resolve() only Lit(Quantity) | LitSymbol | Add | Sub | Mul | Div | Call remain.
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
    /// Resolved: fuzzy boolean (e.g. from constant-folded statistical comparison).
    LitFuzzyBool(FuzzyBool),
    /// Resolved: bare symbol (e.g. pi, e). Identifier not found in unit registry.
    LitSymbol(String),
    Add(Box<ExprDef>, Box<ExprDef>),
    Sub(Box<ExprDef>, Box<ExprDef>),
    Mul(Box<ExprDef>, Box<ExprDef>),
    Div(Box<ExprDef>, Box<ExprDef>),
    /// Comparison: ==, !=, <, <=, >, >=. Result is FuzzyBool (Value::FuzzyBool).
    Eq(Box<ExprDef>, Box<ExprDef>),
    Ne(Box<ExprDef>, Box<ExprDef>),
    Lt(Box<ExprDef>, Box<ExprDef>),
    Le(Box<ExprDef>, Box<ExprDef>),
    Gt(Box<ExprDef>, Box<ExprDef>),
    Ge(Box<ExprDef>, Box<ExprDef>),
    /// Unary minus (e.g. "-1", "-(2 * 3)").
    Neg(Box<ExprDef>),
    /// Function call (e.g. sin(x), max(1, 2)). Name and args; args are positional or named.
    Call(String, Vec<CallArg>),
    /// Unit conversion: left expr evaluated to quantity, right expr is unit-only (e.g. "10 km as m").
    As(Box<ExprDef>, Box<ExprDef>),
    /// Vector literal: `[ expr, expr, ... ]`.
    VecLiteral(Vec<ExprDef>),
    /// Postfix transpose: `expr'` (e.g. [1,2,3]'). Inner must evaluate to a vector.
    Transpose(Box<ExprDef>),
    /// Conditional: if condition then expression else expression. Condition must evaluate to FuzzyBool.
    If(Box<ExprDef>, Box<ExprDef>, Box<ExprDef>),
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
    LitFuzzyBool(FuzzyBool),
    LitSymbol(String),
    Add(Expression<'db>, Expression<'db>),
    Sub(Expression<'db>, Expression<'db>),
    Mul(Expression<'db>, Expression<'db>),
    Div(Expression<'db>, Expression<'db>),
    Eq(Expression<'db>, Expression<'db>),
    Ne(Expression<'db>, Expression<'db>),
    Lt(Expression<'db>, Expression<'db>),
    Le(Expression<'db>, Expression<'db>),
    Gt(Expression<'db>, Expression<'db>),
    Ge(Expression<'db>, Expression<'db>),
    Neg(Expression<'db>),
    /// Function call: name and args as (param name if named, expression).
    Call(String, Vec<(Option<String>, Expression<'db>)>),
    /// Unit conversion: left value, right unit expression.
    As(Expression<'db>, Expression<'db>),
    /// Vector literal: list of element expressions.
    VecLiteral(Vec<Expression<'db>>),
    /// Postfix transpose: inner must evaluate to a vector.
    Transpose(Expression<'db>),
    /// Conditional: condition, then_branch, else_branch.
    If(Expression<'db>, Expression<'db>, Expression<'db>),
}
