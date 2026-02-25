//! IR: inputs and tracked expression graph for the reactive computation.

use crate::error::Span;
use crate::fuzzy::FuzzyBool;
use crate::quantity::Quantity;
use ordered_float::OrderedFloat;

/// Numeric literal with raw string for implicit significant-figure variance.
/// Variance is derived from the number of decimal places in the source (mantissa only).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct NumLiteral {
    /// Exact string as typed (preserves trailing zeros and decimal places).
    pub raw: String,
    /// Parsed value (central value for the distribution).
    pub value: OrderedFloat<f64>,
}

impl NumLiteral {
    /// Number of digits after the decimal point in the mantissa (before any 'e' or 'E').
    pub fn decimal_places_after(&self) -> Option<usize> {
        let mantissa = self.raw.split_once(|c| ['e', 'E'].contains(&c)).map(|(m, _)| m).unwrap_or(self.raw.as_str());
        let dot = mantissa.find('.')?;
        Some(mantissa[dot + 1..].chars().filter(|c| c.is_ascii_digit()).count())
    }

    /// Implicit absolute error from significant figures: no decimal point → 0.5; N decimals → 5×10^−(N+1).
    pub fn implicit_absolute_error(&self) -> f64 {
        match self.decimal_places_after() {
            None => 0.5,
            Some(n) => 5.0 * 10.0_f64.powi(-(n as i32 + 1)),
        }
    }

    /// Variance = (implicit absolute error)².
    pub fn implicit_variance(&self) -> f64 {
        let err = self.implicit_absolute_error();
        err * err
    }

    /// Numeric value as f64.
    pub fn value_f64(&self) -> f64 {
        self.value.0
    }

    /// Build a NumLiteral from an f64 (e.g. for tests or programmatic construction). Raw string is format!("{x}").
    pub fn from_f64(x: f64) -> Self {
        Self {
            raw: format!("{x}"),
            value: OrderedFloat::from(x),
        }
    }
}

/// A single argument in a function call: either positional or named.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum CallArg {
    /// Positional argument (e.g. `1` in `max(1, 2)`).
    Positional(Box<ExprDef>),
    /// Named argument (e.g. `b: 2` in `max(a: 1, b: 2)`).
    Named(String, Box<ExprDef>),
}

/// Call argument with source span (used in spanned AST from parser).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SpannedCallArg {
    Positional(Box<SpannedExprDef>),
    Named(String, Box<SpannedExprDef>),
}

/// Expression definition with source span. Parser produces this; pipeline preserves spans.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SpannedExprDef {
    pub span: Span,
    pub value: SpannedExprDefKind,
}

/// Kind of expression (mirrors [ExprDef] but with [SpannedExprDef] for children).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SpannedExprDefKind {
    LitScalar(NumLiteral),
    LitWithUnit(NumLiteral, String),
    LitUnit(String),
    Lit(Quantity),
    LitFuzzyBool(FuzzyBool),
    LitSymbol(String),
    Add(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Sub(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Mul(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Div(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Eq(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Ne(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Lt(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Le(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Gt(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Ge(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Neg(Box<SpannedExprDef>),
    Call(String, Vec<SpannedCallArg>),
    Lambda(Vec<(String, Option<Box<SpannedExprDef>>)>, Box<SpannedExprDef>),
    CallExpr(Box<SpannedExprDef>, Vec<SpannedCallArg>),
    As(Box<SpannedExprDef>, Box<SpannedExprDef>),
    VecLiteral(Vec<SpannedExprDef>),
    Transpose(Box<SpannedExprDef>),
    Index(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Member(Box<SpannedExprDef>, String),
    MethodCall(Box<SpannedExprDef>, String, Vec<SpannedCallArg>),
    If(Box<SpannedExprDef>, Box<SpannedExprDef>, Box<SpannedExprDef>),
    WithPrecision(Box<SpannedExprDef>, Box<SpannedExprDef>),
    Block(Vec<SpannedExprDef>),
    Binding(String, Box<SpannedExprDef>),
}

impl SpannedExprDef {
    /// Strip spans and return plain [ExprDef] (for transition or when spans are not needed).
    pub fn to_expr_def(&self) -> ExprDef {
        match &self.value {
            SpannedExprDefKind::LitScalar(n) => ExprDef::LitScalar(n.clone()),
            SpannedExprDefKind::LitWithUnit(n, s) => ExprDef::LitWithUnit(n.clone(), s.clone()),
            SpannedExprDefKind::LitUnit(s) => ExprDef::LitUnit(s.clone()),
            SpannedExprDefKind::Lit(q) => ExprDef::Lit(q.clone()),
            SpannedExprDefKind::LitFuzzyBool(f) => ExprDef::LitFuzzyBool(f.clone()),
            SpannedExprDefKind::LitSymbol(s) => ExprDef::LitSymbol(s.clone()),
            SpannedExprDefKind::Add(l, r) => ExprDef::Add(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Sub(l, r) => ExprDef::Sub(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Mul(l, r) => ExprDef::Mul(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Div(l, r) => ExprDef::Div(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Eq(l, r) => ExprDef::Eq(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Ne(l, r) => ExprDef::Ne(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Lt(l, r) => ExprDef::Lt(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Le(l, r) => ExprDef::Le(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Gt(l, r) => ExprDef::Gt(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Ge(l, r) => ExprDef::Ge(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::Neg(inner) => ExprDef::Neg(Box::new(inner.to_expr_def())),
            SpannedExprDefKind::Call(name, args) => ExprDef::Call(
                name.clone(),
                args.iter()
                    .map(|a| match a {
                        SpannedCallArg::Positional(e) => CallArg::Positional(Box::new(e.to_expr_def())),
                        SpannedCallArg::Named(n, e) => CallArg::Named(n.clone(), Box::new(e.to_expr_def())),
                    })
                    .collect(),
            ),
            SpannedExprDefKind::Lambda(params, body) => ExprDef::Lambda(
                params
                    .iter()
                    .map(|(s, o)| (s.clone(), o.as_ref().map(|e| Box::new(e.to_expr_def()))))
                    .collect(),
                Box::new(body.to_expr_def()),
            ),
            SpannedExprDefKind::CallExpr(callee, args) => ExprDef::CallExpr(
                Box::new(callee.to_expr_def()),
                args.iter()
                    .map(|a| match a {
                        SpannedCallArg::Positional(e) => CallArg::Positional(Box::new(e.to_expr_def())),
                        SpannedCallArg::Named(n, e) => CallArg::Named(n.clone(), Box::new(e.to_expr_def())),
                    })
                    .collect(),
            ),
            SpannedExprDefKind::As(l, r) => ExprDef::As(Box::new(l.to_expr_def()), Box::new(r.to_expr_def())),
            SpannedExprDefKind::VecLiteral(elems) => ExprDef::VecLiteral(elems.iter().map(|e| e.to_expr_def()).collect()),
            SpannedExprDefKind::Transpose(inner) => ExprDef::Transpose(Box::new(inner.to_expr_def())),
            SpannedExprDefKind::Index(base, index) => {
                ExprDef::Index(Box::new(base.to_expr_def()), Box::new(index.to_expr_def()))
            }
            SpannedExprDefKind::Member(base, name) => ExprDef::Member(Box::new(base.to_expr_def()), name.clone()),
            SpannedExprDefKind::MethodCall(base, name, args) => ExprDef::MethodCall(
                Box::new(base.to_expr_def()),
                name.clone(),
                args.iter()
                    .map(|a| match a {
                        SpannedCallArg::Positional(e) => CallArg::Positional(Box::new(e.to_expr_def())),
                        SpannedCallArg::Named(n, e) => CallArg::Named(n.clone(), Box::new(e.to_expr_def())),
                    })
                    .collect(),
            ),
            SpannedExprDefKind::If(cond, then_b, else_b) => ExprDef::If(
                Box::new(cond.to_expr_def()),
                Box::new(then_b.to_expr_def()),
                Box::new(else_b.to_expr_def()),
            ),
            SpannedExprDefKind::WithPrecision(l, r) => {
                ExprDef::WithPrecision(Box::new(l.to_expr_def()), Box::new(r.to_expr_def()))
            }
            SpannedExprDefKind::Block(list) => ExprDef::Block(list.iter().map(|e| e.to_expr_def()).collect()),
            SpannedExprDefKind::Binding(name, rhs) => ExprDef::Binding(name.clone(), Box::new(rhs.to_expr_def())),
        }
    }
}

/// Definition of the root expression (plain data, no Salsa).
/// Parser produces LitScalar, LitWithUnit, LitUnit, Call; after resolve() only Lit(Quantity) | LitSymbol | Add | Sub | Mul | Div | Call remain.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ExprDef {
    /// Parsed: bare number (scalar). Carries raw string for implicit variance.
    LitScalar(NumLiteral),
    /// Parsed: number and unit identifier (e.g. "100 m"). Number carries raw string for implicit variance.
    LitWithUnit(NumLiteral, String),
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
    /// User-defined function value: params (name, optional default expr), body.
    Lambda(Vec<(String, Option<Box<ExprDef>>)>, Box<ExprDef>),
    /// Call an expression that evaluates to a function (e.g. ((a,b)=a+b)(1,2)).
    CallExpr(Box<ExprDef>, Vec<CallArg>),
    /// Unit conversion: left expr evaluated to quantity, right expr is unit-only (e.g. "10 km as m").
    As(Box<ExprDef>, Box<ExprDef>),
    /// Vector literal: `[ expr, expr, ... ]`.
    VecLiteral(Vec<ExprDef>),
    /// Postfix transpose: `expr'` (e.g. [1,2,3]'). Inner must evaluate to a vector.
    Transpose(Box<ExprDef>),
    /// Index/single-element access: `V[index]` or `V.0`. Base must be vector; index 0-based; yields scalar.
    Index(Box<ExprDef>, Box<ExprDef>),
    /// Property access: `V.length`. Base and property name; dispatch at eval (e.g. vector.length).
    Member(Box<ExprDef>, String),
    /// Method call: `V.map(fn)`, `V.take(1, 3)`. Base, method name, args; dispatch at eval.
    MethodCall(Box<ExprDef>, String, Vec<CallArg>),
    /// Conditional: if condition then expression else expression. Condition must evaluate to FuzzyBool.
    If(Box<ExprDef>, Box<ExprDef>, Box<ExprDef>),
    /// Explicit precision: left ~ right => value from left with variance = (right.value())². Right must be > 0; right's variance is discarded.
    WithPrecision(Box<ExprDef>, Box<ExprDef>),
    /// Block: sequence of expressions; value is the last expression, or undefined if empty.
    Block(Vec<ExprDef>),
    /// Variable binding (in block context): name = value_expr. Extends scope for subsequent items.
    Binding(String, Box<ExprDef>),
}

/// Input that holds the root expression definition.
/// When [spanned_root] is [Some], runtime errors can report source location (line/column and snippet).
#[salsa::input]
pub struct ProgramDef {
    #[returns(ref)]
    pub root: ExprDef,
    /// Spanned AST for the same root; when set, each expression node gets a span for error reporting.
    #[returns(ref)]
    pub spanned_root: Option<SpannedExprDef>,
}

/// A single expression node in the computation graph (tracked by Salsa).
#[salsa::tracked(debug)]
pub struct Expression<'db> {
    #[returns(ref)]
    pub data: ExprData<'db>,
    /// Source span when built from [ProgramDef::spanned_root]; used for runtime error location.
    pub span: Option<Span>,
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
    /// User-defined function: params (name, optional default expr), body.
    Lambda(Vec<(String, Option<Expression<'db>>)>, Expression<'db>),
    /// Call an expression that evaluates to a function.
    CallExpr(Expression<'db>, Vec<(Option<String>, Expression<'db>)>),
    /// Unit conversion: left value, right unit expression.
    As(Expression<'db>, Expression<'db>),
    /// Vector literal: list of element expressions.
    VecLiteral(Vec<Expression<'db>>),
    /// Postfix transpose: inner must evaluate to a vector.
    Transpose(Expression<'db>),
    /// Index/single-element access: base must be vector, index 0-based; yields scalar.
    Index(Expression<'db>, Expression<'db>),
    /// Property access: base and property name (e.g. vector.length).
    Member(Expression<'db>, String),
    /// Method call: base, method name, args (e.g. vector.map(fn), vector.take(1, 3)).
    MethodCall(Expression<'db>, String, Vec<(Option<String>, Expression<'db>)>),
    /// Conditional: condition, then_branch, else_branch.
    If(Expression<'db>, Expression<'db>, Expression<'db>),
    /// Explicit precision: left ~ right (use right's value as absolute error; variance = error²).
    WithPrecision(Expression<'db>, Expression<'db>),
    /// Block: sequence of expressions; value is the last, or undefined if empty.
    Block(Vec<Expression<'db>>),
    /// Variable binding (in block context): name = value_expr.
    Binding(String, Expression<'db>),
}
