//! Shared LSP state: document, Salsa DB, and diagnostics.

use crate::mapping::{run_error_to_diagnostic, span_to_range};
use tower_lsp::lsp_types::{Diagnostic, InlayHint, Position, Range, Url};
use snaq_lite_lang::{
    cas, default_si_registry, empty_scope, format_value_for_display, parse, program,
    set_eval_registry, set_stream_input_registry, ExprDef, Expression, ProgramDef, UnitRegistry,
};

/// Internal LSP state (held under async lock).
pub struct LspState {
    db: salsa::DatabaseImpl,
    source: String,
    uri: Option<Url>,
    version: Option<i32>,
    root_def: Option<ExprDef>,
    root_spanned: Option<snaq_lite_lang::SpannedExprDef>,
    unit_registry: UnitRegistry,
    /// Cached diagnostics from last parse/resolve/simplify.
    diagnostics: Vec<Diagnostic>,
}

fn empty_block_def() -> ExprDef {
    ExprDef::Block(vec![])
}

impl LspState {
    pub fn new() -> Self {
        Self {
            db: salsa::DatabaseImpl::new(),
            source: String::new(),
            uri: None,
            version: None,
            root_def: None,
            root_spanned: None,
            unit_registry: default_si_registry(),
            diagnostics: Vec::new(),
        }
    }

    /// Update document content and re-parse/resolve/simplify; update diagnostics.
    pub fn update_document(&mut self, uri: Url, version: i32, text: &str) {
        self.source = text.to_string();
        self.uri = Some(uri);
        self.version = Some(version);

        if text.trim().is_empty() {
            self.root_def = Some(empty_block_def());
            self.root_spanned = None;
            self.diagnostics = Vec::new();
            return;
        }

        let mut diags = Vec::new();
        match parse(text) {
            Err(pe) => {
                let err = snaq_lite_lang::RunError::from(pe);
                diags.push(run_error_to_diagnostic(&err, text));
                self.root_def = Some(empty_block_def());
                self.root_spanned = None;
            }
            Ok(spanned) => {
                set_eval_registry(self.unit_registry.clone());
                set_stream_input_registry(snaq_lite_lang::StreamInputRegistry::new(
                    &self.db,
                    std::collections::HashMap::new(),
                ));
                match snaq_lite_lang::resolve::resolve(spanned.clone(), &self.unit_registry) {
                    Err(e) => {
                        diags.push(run_error_to_diagnostic(&e, text));
                        self.root_def = Some(empty_block_def());
                        self.root_spanned = None;
                    }
                    Ok(resolved) => match cas::simplify_symbolic(resolved.clone(), &self.unit_registry) {
                        Err(e) => {
                            diags.push(run_error_to_diagnostic(&e, text));
                            self.root_def = Some(resolved.to_expr_def());
                            self.root_spanned = Some(resolved);
                        }
                        Ok(simplified) => {
                            let root_def = simplified.to_expr_def();
                            let program_def =
                                ProgramDef::new(&self.db, root_def.clone(), Some(simplified.clone()));
                            let _root_expr = program(&self.db, program_def);
                            self.root_def = Some(root_def);
                            self.root_spanned = Some(simplified);
                        }
                    },
                }
            }
        }
        self.diagnostics = diags;
    }

    pub fn document_version(&self) -> Option<i32> {
        self.version
    }

    /// Return current diagnostics (after last update_document).
    pub fn diagnostics(&self) -> Vec<Diagnostic> {
        self.diagnostics.clone()
    }

    /// Hover at (line, character) - 0-based. Returns (formatted value, optional range for highlighting) or None.
    pub fn hover_at(&self, uri: &Url, line: u32, character: u32) -> Option<(String, Option<Range>)> {
        if self.uri.as_ref() != Some(uri) || self.source.is_empty() {
            return None;
        }
        let root_def = self.root_def.as_ref()?;
        let root_spanned = self.root_spanned.clone();
        set_eval_registry(self.unit_registry.clone());
        set_stream_input_registry(snaq_lite_lang::StreamInputRegistry::new(
            &self.db,
            std::collections::HashMap::new(),
        ));
        let program_def = ProgramDef::new(&self.db, root_def.clone(), root_spanned);
        let root = program(&self.db, program_def);
        let offset = position_to_byte_offset(&self.source, line, character)?;
        let expr = expression_at_offset(&self.db, root, offset)?;
        let range = expr
            .span(&self.db)
            .map(|s| span_to_range(&s, &self.source));
        let scope = empty_scope(&self.db);
        let value = snaq_lite_lang::value(&self.db, scope, expr).ok()?;
        let content = format_value_for_display(&self.db, &value).ok()?;
        Some((content, range))
    }

    /// Inlay hints for the document.
    pub fn inlay_hints(&self, uri: &Url) -> Vec<InlayHint> {
        if self.uri.as_ref() != Some(uri) || self.source.is_empty() {
            return Vec::new();
        }
        let Some(root_def) = self.root_def.as_ref() else {
            return Vec::new();
        };
        set_eval_registry(self.unit_registry.clone());
        set_stream_input_registry(snaq_lite_lang::StreamInputRegistry::new(
            &self.db,
            std::collections::HashMap::new(),
        ));
        let program_def = ProgramDef::new(
            &self.db,
            root_def.clone(),
            self.root_spanned.clone(),
        );
        let root = program(&self.db, program_def);
        collect_inlay_hints(&self.db, &self.source, root)
    }
}

impl Default for LspState {
    fn default() -> Self {
        Self::new()
    }
}

/// Convert 0-based line and character (byte) to byte offset.
fn position_to_byte_offset(source: &str, line: u32, character: u32) -> Option<usize> {
    let mut offset = 0;
    for (i, chunk) in source.lines().enumerate() {
        if i == line as usize {
            let char_off = character as usize;
            return Some(offset + char_off.min(chunk.len()));
        }
        offset += chunk.len() + 1;
    }
    Some(offset)
}

/// Find smallest expression that contains the given byte offset.
fn expression_at_offset<'db>(
    db: &'db dyn salsa::Database,
    expr: Expression<'db>,
    offset: usize,
) -> Option<Expression<'db>> {
    use snaq_lite_lang::ir::ExprData;
    let span = expr.span(db)?;
    if offset < span.start || offset >= span.end {
        return None;
    }
    match expr.data(db) {
        ExprData::Block(children) => {
            for c in children {
                if let Some(found) = expression_at_offset(db, *c, offset) {
                    return Some(found);
                }
            }
            Some(expr)
        }
        ExprData::Add(a, b)
        | ExprData::Sub(a, b)
        | ExprData::Mul(a, b)
        | ExprData::Div(a, b)
        | ExprData::Eq(a, b)
        | ExprData::Ne(a, b)
        | ExprData::Lt(a, b)
        | ExprData::Le(a, b)
        | ExprData::Gt(a, b)
        | ExprData::Ge(a, b)
        | ExprData::And(a, b)
        | ExprData::As(a, b) => {
            expression_at_offset(db, *a, offset)
                .or_else(|| expression_at_offset(db, *b, offset))
                .or(Some(expr))
        }
        ExprData::Neg(e)
        | ExprData::Transpose(e) => expression_at_offset(db, *e, offset).or(Some(expr)),
        ExprData::Call(_, args) | ExprData::CallExpr(_, args) => {
            for (_, arg) in args {
                if let Some(found) = expression_at_offset(db, *arg, offset) {
                    return Some(found);
                }
            }
            Some(expr)
        }
        ExprData::Lambda(params, body) => {
            for (_, default) in params {
                if let Some(e) = default {
                    if let Some(found) = expression_at_offset(db, *e, offset) {
                        return Some(found);
                    }
                }
            }
            expression_at_offset(db, *body, offset).or(Some(expr))
        }
        ExprData::VecLiteral(exprs) => {
            for e in exprs {
                if let Some(found) = expression_at_offset(db, *e, offset) {
                    return Some(found);
                }
            }
            Some(expr)
        }
        ExprData::Index(base, _) | ExprData::Member(base, _) => {
            expression_at_offset(db, *base, offset).or(Some(expr))
        }
        ExprData::MethodCall(base, _, args) => {
            if let Some(found) = expression_at_offset(db, *base, offset) {
                return Some(found);
            }
            for (_, arg) in args {
                if let Some(found) = expression_at_offset(db, *arg, offset) {
                    return Some(found);
                }
            }
            Some(expr)
        }
        ExprData::If(cond, then_e, else_e) => {
            expression_at_offset(db, *cond, offset)
                .or_else(|| expression_at_offset(db, *then_e, offset))
                .or_else(|| expression_at_offset(db, *else_e, offset))
                .or(Some(expr))
        }
        ExprData::WithPrecision(l, r) => {
            expression_at_offset(db, *l, offset)
                .or_else(|| expression_at_offset(db, *r, offset))
                .or(Some(expr))
        }
        ExprData::Binding(_, e) => expression_at_offset(db, *e, offset).or(Some(expr)),
        ExprData::MapLiteral(entries) => {
            for (_, e) in entries {
                if let Some(found) = expression_at_offset(db, *e, offset) {
                    return Some(found);
                }
            }
            Some(expr)
        }
        _ => Some(expr),
    }
}

/// Collect inlay hints by walking the expression tree.
fn collect_inlay_hints(
    db: &dyn salsa::Database,
    source: &str,
    root: Expression<'_>,
) -> Vec<InlayHint> {
    let mut hints = Vec::new();
    collect_inlay_hints_rec(db, source, root, &mut hints);
    hints
}

fn collect_inlay_hints_rec<'db>(
    db: &'db dyn salsa::Database,
    source: &str,
    expr: Expression<'db>,
    out: &mut Vec<InlayHint>,
) {
    use tower_lsp::lsp_types::InlayHintKind;
    use snaq_lite_lang::ir::ExprData;

    if let Some(span) = expr.span(db) {
        let (line_1, col_1) = span.line_col(source);
        let line_0 = line_1.saturating_sub(1);
        let col_0 = col_1;
        let scope = empty_scope(db);
        if let Ok(val) = snaq_lite_lang::value(db, scope, expr) {
            if let Ok(s) = format_value_for_display(db, &val) {
                if !s.is_empty() && s != "<vector>" && s != "<function>" && s != "<map>" {
                    out.push(InlayHint {
                        position: Position {
                            line: line_0,
                            character: col_0 + (span.end.saturating_sub(span.start)) as u32,
                        },
                        label: tower_lsp::lsp_types::InlayHintLabel::String(format!(" → {s}")),
                        kind: Some(InlayHintKind::TYPE),
                        text_edits: None,
                        tooltip: None,
                        padding_left: Some(false),
                        padding_right: Some(false),
                        data: None,
                    });
                }
            }
        }
    }
    if let ExprData::Block(children) = expr.data(db) {
        for c in children {
            collect_inlay_hints_rec(db, source, *c, out);
        }
    }
}
