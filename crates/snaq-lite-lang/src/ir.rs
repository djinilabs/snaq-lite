//! IR: inputs and tracked expression graph for the reactive computation.

/// The two numeric arguments to the computation.
#[salsa::input]
pub struct Numbers {
    pub a: i64,
    pub b: i64,
}

/// Definition of the root expression (plain data, no Salsa).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExprDef {
    LitA,
    LitB,
    Add(Box<ExprDef>, Box<ExprDef>),
    Sub(Box<ExprDef>, Box<ExprDef>),
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
    LitA,
    LitB,
    Add(Expression<'db>, Expression<'db>),
    Sub(Expression<'db>, Expression<'db>),
}
