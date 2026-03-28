//! Shared LSP state: multi-document map, Salsa DB, and diagnostics.

use crate::mapping::{run_error_to_diagnostic, span_to_range};
use crate::position;
use snaq_lite_lang::{
    cas, default_si_registry, empty_scope, format_value_for_display, parse, program,
    set_eval_registry, set_stream_input_registry, ExprDef, Expression, ProgramDef, UnitRegistry,
};
use std::collections::{HashMap, HashSet};
use tower_lsp::lsp_types::{
    Diagnostic, DocumentSymbol, InlayHint, Location, Position, Range, SymbolKind,
    TextDocumentContentChangeEvent, Url,
};

/// Per-document state (one entry per open virtual or physical URI).
#[derive(Clone)]
pub struct DocumentEntry {
    pub source: String,
    pub version: Option<i32>,
    pub root_def: Option<ExprDef>,
    pub root_spanned: Option<snaq_lite_lang::SpannedExprDef>,
    /// True when parse() succeeded for this document version.
    /// Reconciliation logic uses this to avoid pruning graph edges on transient syntax errors.
    pub parse_succeeded: bool,
    pub diagnostics: Vec<Diagnostic>,
}

/// Internal LSP state (held under async lock). Tracks multiple documents by URI (e.g. snaq://graph/node_42.sl).
pub struct LspState {
    db: salsa::DatabaseImpl,
    /// Map from document URI to parsed/resolved state and diagnostics.
    documents: HashMap<Url, DocumentEntry>,
    unit_registry: UnitRegistry,
}

fn empty_block_def() -> ExprDef {
    ExprDef::Block(vec![])
}

impl LspState {
    pub fn new() -> Self {
        Self {
            db: salsa::DatabaseImpl::new(),
            documents: HashMap::new(),
            unit_registry: default_si_registry(),
        }
    }

    /// Update document content and re-parse/resolve/simplify; update diagnostics for this URI.
    pub fn update_document(&mut self, uri: Url, version: i32, text: &str) {
        let entry = self.parse_document(version, text);
        self.documents.insert(uri, entry);
    }

    /// Apply incremental or full-content changes to an open document, then re-parse.
    pub fn apply_document_changes(
        &mut self,
        uri: Url,
        version: i32,
        changes: &[TextDocumentContentChangeEvent],
    ) {
        let Some(existing) = self.documents.get(&uri) else {
            return;
        };
        let mut text = existing.source.clone();
        for change in changes {
            if let Some(range) = change.range {
                let Some(span) = position::range_to_span(&text, &range) else {
                    continue;
                };
                if span.start <= span.end
                    && span.end <= text.len()
                    && text.is_char_boundary(span.start)
                    && text.is_char_boundary(span.end)
                {
                    text.replace_range(span.start..span.end, &change.text);
                }
            } else {
                text = change.text.clone();
            }
        }
        let entry = self.parse_document(version, &text);
        self.documents.insert(uri, entry);
    }

    fn parse_document(&self, version: i32, text: &str) -> DocumentEntry {
        if text.trim().is_empty() {
            return DocumentEntry {
                source: text.to_string(),
                version: Some(version),
                root_def: Some(empty_block_def()),
                root_spanned: None,
                parse_succeeded: true,
                diagnostics: Vec::new(),
            };
        }

        let mut diags = Vec::new();
        let (root_def, root_spanned, parse_succeeded) = match parse(text) {
            Err(pe) => {
                let err = snaq_lite_lang::RunError::from(pe);
                diags.push(run_error_to_diagnostic(&err, text));
                (empty_block_def(), None, false)
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
                        (spanned.to_expr_def(), Some(spanned), true)
                    }
                    Ok(resolved) => {
                        match cas::simplify_symbolic(resolved.clone(), &self.unit_registry) {
                            Err(e) => {
                                diags.push(run_error_to_diagnostic(&e, text));
                                (resolved.to_expr_def(), Some(resolved), true)
                            }
                            Ok(simplified) => {
                                let root_def = simplified.to_expr_def();
                                let program_def = ProgramDef::new(
                                    &self.db,
                                    root_def.clone(),
                                    Some(simplified.clone()),
                                );
                                let _root_expr = program(&self.db, program_def);
                                (root_def, Some(simplified), true)
                            }
                        }
                    }
                }
            }
        };

        DocumentEntry {
            source: text.to_string(),
            version: Some(version),
            root_def: Some(root_def),
            root_spanned,
            parse_succeeded,
            diagnostics: diags,
        }
    }

    /// Document version for the given URI, if open.
    pub fn document_version(&self, uri: &Url) -> Option<i32> {
        self.documents.get(uri).and_then(|e| e.version)
    }

    /// Set of open document URIs (for graph topological order).
    pub fn document_uris(&self) -> HashSet<Url> {
        self.documents.keys().cloned().collect()
    }

    /// Whether the given URI is open (for pub-sub subscription validation).
    pub fn has_document(&self, uri: &Url) -> bool {
        self.documents.contains_key(uri)
    }

    /// Document entry for the given URI, if open. Used for graph node signature and similar.
    pub fn get_document(&self, uri: &Url) -> Option<&DocumentEntry> {
        self.documents.get(uri)
    }

    /// Source text for the given URI, if open. Returns empty string if not found.
    pub fn source(&self, uri: &Url) -> String {
        self.documents
            .get(uri)
            .map(|e| e.source.clone())
            .unwrap_or_default()
    }

    /// Unit registry (for run_with_stream_inputs in subscribe).
    pub fn unit_registry(&self) -> &UnitRegistry {
        &self.unit_registry
    }

    /// Database instance (for fetchResultSlice and other operations that need to read cached values).
    pub fn db(&self) -> &salsa::DatabaseImpl {
        &self.db
    }

    /// Return current diagnostics for the given URI.
    pub fn diagnostics(&self, uri: &Url) -> Vec<Diagnostic> {
        self.documents
            .get(uri)
            .map(|e| e.diagnostics.clone())
            .unwrap_or_default()
    }

    /// Hover at (line, character) - 0-based. Returns (formatted value, optional range for highlighting) or None.
    pub fn hover_at(
        &self,
        uri: &Url,
        line: u32,
        character: u32,
    ) -> Option<(String, Option<Range>)> {
        let doc = self.documents.get(uri)?;
        let source = &doc.source;
        if source.is_empty() {
            return None;
        }
        let root_def = doc.root_def.as_ref()?;
        let root_spanned = doc.root_spanned.clone();
        set_eval_registry(self.unit_registry.clone());
        set_stream_input_registry(snaq_lite_lang::StreamInputRegistry::new(
            &self.db,
            std::collections::HashMap::new(),
        ));
        let program_def = ProgramDef::new(&self.db, root_def.clone(), root_spanned);
        let root = program(&self.db, program_def);
        let offset = position::position_to_byte_offset(source, Position { line, character })?;
        let expr = expression_at_offset(&self.db, root, offset)?;
        let range = expr.span(&self.db).map(|s| span_to_range(&s, source));
        let scope = empty_scope(&self.db);
        let value = snaq_lite_lang::value(&self.db, scope, expr).ok()?;
        let content = format_value_for_display(&self.db, &value).ok()?;
        Some((content, range))
    }

    /// Inlay hints for the document at the given URI.
    pub fn inlay_hints(&self, uri: &Url) -> Vec<InlayHint> {
        let doc = match self.documents.get(uri) {
            Some(d) => d,
            None => return Vec::new(),
        };
        if doc.source.is_empty() {
            return Vec::new();
        }
        let Some(root_def) = doc.root_def.as_ref() else {
            return Vec::new();
        };
        set_eval_registry(self.unit_registry.clone());
        set_stream_input_registry(snaq_lite_lang::StreamInputRegistry::new(
            &self.db,
            std::collections::HashMap::new(),
        ));
        let program_def = ProgramDef::new(&self.db, root_def.clone(), doc.root_spanned.clone());
        let root = program(&self.db, program_def);
        collect_inlay_hints(&self.db, &doc.source, root)
    }

    /// Identifier at a given document position.
    pub fn identifier_at(&self, uri: &Url, line: u32, character: u32) -> Option<String> {
        let doc = self.documents.get(uri)?;
        let offset = position::position_to_byte_offset(&doc.source, Position { line, character })?;
        let (start, end) = position::find_identifier_at_offset(&doc.source, offset)?;
        Some(doc.source[start..end].to_string())
    }

    /// Definition locations for an identifier in a URI (best-effort declaration matching).
    pub fn definition_locations(&self, uri: &Url, ident: &str) -> Vec<Location> {
        let Some(doc) = self.documents.get(uri) else {
            return Vec::new();
        };
        let mut locations = Vec::new();
        for (line_idx, line) in doc.source.lines().enumerate() {
            let trimmed = line.trim_start();
            let lead = line.len().saturating_sub(trimmed.len());
            let decl_offset = if let Some(rest) = trimmed.strip_prefix("input ") {
                if starts_with_ident(rest, ident) {
                    Some(lead + "input ".len())
                } else {
                    None
                }
            } else if let Some(rest) = trimmed.strip_prefix("fn ") {
                if starts_with_ident(rest, ident) {
                    Some(lead + "fn ".len())
                } else {
                    None
                }
            } else if starts_with_ident(trimmed, ident) {
                let after = trimmed.get(ident.len()..).unwrap_or("");
                if after.trim_start().starts_with('=') {
                    Some(lead)
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(col) = decl_offset {
                let start = Position {
                    line: line_idx as u32,
                    character: position::byte_offset_to_position(line, col).character,
                };
                let end = Position {
                    line: line_idx as u32,
                    character: position::byte_offset_to_position(line, col + ident.len()).character,
                };
                locations.push(Location {
                    uri: uri.clone(),
                    range: Range { start, end },
                });
            }
        }
        locations
    }

    /// All reference ranges of identifier in one document.
    pub fn reference_ranges(&self, uri: &Url, ident: &str) -> Vec<Range> {
        let Some(doc) = self.documents.get(uri) else {
            return Vec::new();
        };
        if ident.is_empty() {
            return Vec::new();
        }
        let src = doc.source.as_bytes();
        let needle = ident.as_bytes();
        let mut ranges = Vec::new();
        let mut i = 0usize;
        while i + needle.len() <= src.len() {
            if &src[i..i + needle.len()] == needle {
                let left_ok = i == 0 || !is_ident_char(src[i - 1]);
                let right_ok =
                    i + needle.len() == src.len() || !is_ident_char(src[i + needle.len()]);
                if left_ok && right_ok {
                    let start = position::byte_offset_to_position(&doc.source, i);
                    let end = position::byte_offset_to_position(&doc.source, i + needle.len());
                    ranges.push(Range { start, end });
                }
                i += needle.len();
            } else {
                i += 1;
            }
        }
        ranges
    }

    /// Best-effort document symbols (input declarations, bindings, named functions).
    pub fn document_symbols(&self, uri: &Url) -> Vec<DocumentSymbol> {
        let Some(doc) = self.documents.get(uri) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for (line_idx, line) in doc.source.lines().enumerate() {
            let trimmed = line.trim_start();
            let lead = line.len().saturating_sub(trimmed.len());

            let push_symbol = |out: &mut Vec<DocumentSymbol>,
                               name: String,
                               kind: SymbolKind,
                               start_col: usize| {
                let start = Position {
                    line: line_idx as u32,
                    character: position::byte_offset_to_position(line, start_col).character,
                };
                let end = Position {
                    line: line_idx as u32,
                    character: position::byte_offset_to_position(line, start_col + name.len())
                        .character,
                };
                let range = Range { start, end };
                #[allow(deprecated)]
                out.push(DocumentSymbol {
                    name,
                    detail: None,
                    kind,
                    tags: None,
                    deprecated: None,
                    range,
                    selection_range: range,
                    children: None,
                });
            };

            if let Some(rest) = trimmed.strip_prefix("input ") {
                let name = rest
                    .split(':')
                    .next()
                    .unwrap_or("")
                    .split_whitespace()
                    .next()
                    .unwrap_or("")
                    .to_string();
                if !name.is_empty() {
                    push_symbol(&mut out, name, SymbolKind::VARIABLE, lead + "input ".len());
                }
                continue;
            }

            if let Some(rest) = trimmed.strip_prefix("fn ") {
                let name = rest.split(['(', ' ']).next().unwrap_or("").to_string();
                if !name.is_empty() {
                    push_symbol(&mut out, name, SymbolKind::FUNCTION, lead + "fn ".len());
                }
                continue;
            }

            if let Some(eq_pos) = trimmed.find('=') {
                let lhs = trimmed[..eq_pos].trim();
                if !lhs.is_empty() && lhs.bytes().all(is_ident_char) {
                    let start_col = lead + trimmed.find(lhs).unwrap_or(0);
                    push_symbol(&mut out, lhs.to_string(), SymbolKind::VARIABLE, start_col);
                }
            }
        }
        out
    }
}

impl Default for LspState {
    fn default() -> Self {
        Self::new()
    }
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
        | ExprData::As(a, b) => expression_at_offset(db, *a, offset)
            .or_else(|| expression_at_offset(db, *b, offset))
            .or(Some(expr)),
        ExprData::Neg(e) | ExprData::Transpose(e) => {
            expression_at_offset(db, *e, offset).or(Some(expr))
        }
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
        ExprData::If(cond, then_e, else_e) => expression_at_offset(db, *cond, offset)
            .or_else(|| expression_at_offset(db, *then_e, offset))
            .or_else(|| expression_at_offset(db, *else_e, offset))
            .or(Some(expr)),
        ExprData::WithPrecision(l, r) => expression_at_offset(db, *l, offset)
            .or_else(|| expression_at_offset(db, *r, offset))
            .or(Some(expr)),
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
    use snaq_lite_lang::ir::ExprData;
    use tower_lsp::lsp_types::InlayHintKind;

    if let Some(span) = expr.span(db) {
        let end_pos = position::byte_offset_to_position(source, span.end);
        let scope = empty_scope(db);
        if let Ok(val) = snaq_lite_lang::value(db, scope, expr) {
            if let Ok(s) = format_value_for_display(db, &val) {
                if !s.is_empty() && s != "<vector>" && s != "<function>" && s != "<map>" {
                    out.push(InlayHint {
                        position: end_pos,
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

fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn starts_with_ident(s: &str, ident: &str) -> bool {
    if !s.starts_with(ident) {
        return false;
    }
    let next = s.as_bytes().get(ident.len()).copied();
    !next.is_some_and(is_ident_char)
}
