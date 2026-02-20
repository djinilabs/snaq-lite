//! IR: inputs and tracked expression graph for the reactive computation.

/// Definition of the root expression (plain data, no Salsa).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExprDef {
    Lit(i64),
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
    Lit(i64),
    Add(Expression<'db>, Expression<'db>),
    Sub(Expression<'db>, Expression<'db>),
}
