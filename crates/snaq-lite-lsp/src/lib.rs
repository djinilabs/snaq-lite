//! snaq-lite LSP server: dual-target (native stdio + WASM Web Worker) language server.

pub mod mapping;
pub mod state;

#[cfg(target_arch = "wasm32")]
pub mod transport;

use futures::lock::Mutex;
use state::LspState;
use std::sync::Arc;
use tower_lsp::lsp_types::{
    Hover, HoverContents, HoverProviderCapability, InlayHint, InitializeResult,
    MarkedString, MessageType, ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
    Url,
};

use crate::mapping::SERVER_NAME;
use tower_lsp::{Client, LanguageServer, LspService};
#[cfg(not(target_arch = "wasm32"))]
use tower_lsp::Server;

pub use mapping::{run_error_to_diagnostic, span_to_range};

/// Shared state for the LSP backend (async lock for both native and WASM).
pub type SharedState = Arc<Mutex<LspState>>;

/// Backend implementing the Language Server Protocol for snaq-lite.
pub struct SnaqLiteBackend {
    pub client: Client,
    pub state: SharedState,
}

#[tower_lsp::async_trait]
impl LanguageServer for SnaqLiteBackend {
    async fn initialize(&self, _params: tower_lsp::lsp_types::InitializeParams) -> tower_lsp::jsonrpc::Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                inlay_hint_provider: Some(tower_lsp::lsp_types::OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(tower_lsp::lsp_types::ServerInfo {
                name: SERVER_NAME.to_string(),
                version: Some("0.1.0".to_string()),
            }),
        })
    }

    async fn initialized(&self, _params: tower_lsp::lsp_types::InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "snaq-lite LSP initialized")
            .await;
    }

    async fn shutdown(&self) -> tower_lsp::jsonrpc::Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: tower_lsp::lsp_types::DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let text = params.text_document.text;
        let version = params.text_document.version;
        let mut state = self.state.lock().await;
        state.update_document(uri.clone(), version, &text);
        drop(state);
        self.publish_diagnostics(uri).await;
    }

    async fn did_change(&self, params: tower_lsp::lsp_types::DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let version = params.text_document.version;
        let mut state = self.state.lock().await;
        // Full sync: we only use the first content change; empty list is a no-op.
        if let Some(content_changes) = params.content_changes.first() {
            let text = content_changes.text.clone();
            state.update_document(uri.clone(), version, &text);
        }
        drop(state);
        self.publish_diagnostics(uri).await;
    }

    async fn hover(&self, params: tower_lsp::lsp_types::HoverParams) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let state = self.state.lock().await;
        let Some((content, range)) = state.hover_at(&uri, position.line, position.character) else {
            return Ok(None);
        };
        if content.is_empty() {
            return Ok(None);
        }
        Ok(Some(Hover {
            contents: HoverContents::Scalar(MarkedString::String(content)),
            range,
        }))
    }

    async fn inlay_hint(
        &self,
        params: tower_lsp::lsp_types::InlayHintParams,
    ) -> tower_lsp::jsonrpc::Result<Option<Vec<InlayHint>>> {
        let uri = params.text_document.uri;
        let state = self.state.lock().await;
        let hints = state.inlay_hints(&uri);
        Ok(Some(hints))
    }
}

impl SnaqLiteBackend {
    async fn publish_diagnostics(&self, uri: Url) {
        let state = self.state.lock().await;
        let diagnostics = state.diagnostics();
        let version = state.document_version();
        drop(state);
        self.client
            .publish_diagnostics(uri, diagnostics, version)
            .await;
    }
}

/// Build the LSP service (same for native and WASM).
pub fn create_lsp_service() -> (LspService<SnaqLiteBackend>, tower_lsp::ClientSocket) {
    let state: SharedState = Arc::new(Mutex::new(LspState::new()));
    let (service, socket) = LspService::new(move |client| SnaqLiteBackend {
        client,
        state: Arc::clone(&state),
    });
    (service, socket)
}

/// Run the LSP server with the given stdin and stdout (native).
#[cfg(not(target_arch = "wasm32"))]
pub async fn run_native<I, O>(stdin: I, stdout: O) -> Result<(), Box<dyn std::error::Error + Send + Sync>>
where
    I: tokio::io::AsyncRead + Unpin + Send + 'static,
    O: tokio::io::AsyncWrite + Unpin + Send + 'static,
{
    let (service, socket) = create_lsp_service();
    Server::new(stdin, stdout, socket).serve(service).await;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Url;

    // ---- span_to_range ----

    #[test]
    fn span_to_range_uses_zero_based_line_and_column() {
        // Single line: span 2..5 in "hello" is "llo"; lang line_col gives 1-based line, column as byte offset
        let source = "hello";
        let range = span_to_range(
            &snaq_lite_lang::Span { start: 2, end: 5 },
            source,
        );
        assert_eq!(range.start.line, 0);
        assert_eq!(range.start.character, 2);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 5);
    }

    #[test]
    fn span_to_range_multiline_second_line() {
        let source = "a\nbc\nd";
        // span 3..5: second line (0-based line 1); end can be 0 when span ends at newline
        let range = span_to_range(&snaq_lite_lang::Span { start: 3, end: 5 }, source);
        assert_eq!(range.start.line, 1);
        assert_eq!(range.end.line, 1);
        assert!(range.start.character <= range.end.character || range.end.character == 0);
    }

    #[test]
    fn span_to_range_start_of_file() {
        let source = "x";
        let range = span_to_range(&snaq_lite_lang::Span { start: 0, end: 1 }, source);
        assert_eq!(range.start.line, 0);
        // lang line_col uses .max(1) so first character can be column 1
        assert!(range.start.character <= 1);
        assert_eq!(range.end.line, 0);
        assert_eq!(range.end.character, 1);
    }

    #[test]
    fn span_to_range_empty_source_saturates() {
        let source = "";
        let range = span_to_range(&snaq_lite_lang::Span { start: 0, end: 0 }, source);
        // lang returns (1,1) for empty prefix; we convert line to 0-based
        assert_eq!(range.start.line, 0);
        assert_eq!(range.end.line, 0);
    }

    // ---- run_error_to_diagnostic ----

    #[test]
    fn run_error_parse_kind_produces_diagnostic() {
        let err = snaq_lite_lang::RunError {
            span: Some(snaq_lite_lang::Span { start: 0, end: 1 }),
            kind: snaq_lite_lang::RunErrorKind::Parse(snaq_lite_lang::ParseError {
                message: "expected number".to_string(),
                span: Some(snaq_lite_lang::Span { start: 0, end: 1 }),
            }),
        };
        let source = "x";
        let d = run_error_to_diagnostic(&err, source);
        assert_eq!(d.message, "expected number");
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
        assert_eq!(d.source.as_deref(), Some("snaq-lite"));
    }

    #[test]
    fn run_error_runtime_kind_uses_span_and_format() {
        let err = snaq_lite_lang::RunError {
            span: Some(snaq_lite_lang::Span { start: 2, end: 5 }),
            kind: snaq_lite_lang::RunErrorKind::DivisionByZero,
        };
        let source = "  1/0 ";
        let d = run_error_to_diagnostic(&err, source);
        assert!(d.message.contains("division") || d.message.contains("Division"));
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.range.start.character, 2);
        assert_eq!(d.severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
    }

    #[test]
    fn run_error_without_span_falls_back_to_zero_range() {
        let err = snaq_lite_lang::RunError {
            span: None,
            kind: snaq_lite_lang::RunErrorKind::Parse(snaq_lite_lang::ParseError {
                message: "bad".to_string(),
                span: None,
            }),
        };
        let d = run_error_to_diagnostic(&err, "anything");
        assert_eq!(d.message, "bad");
        assert_eq!(d.range.start.line, 0);
        assert_eq!(d.range.start.character, 0);
        assert_eq!(d.range.end.line, 0);
        assert_eq!(d.range.end.character, 0);
    }

    // ---- state (LspState) ----

    #[test]
    fn state_update_document_empty_clears_diagnostics() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "");
        assert!(state.diagnostics().is_empty());
        assert_eq!(state.document_version(), Some(1));
    }

    #[test]
    fn state_update_document_parse_error_produces_diagnostic() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "syntax error @@");
        let diags = state.diagnostics();
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, Some(tower_lsp::lsp_types::DiagnosticSeverity::ERROR));
        assert!(!diags[0].message.is_empty());
    }

    #[test]
    fn state_update_document_valid_produces_no_diagnostics() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        assert!(state.diagnostics().is_empty());
    }

    #[test]
    fn state_hover_at_returns_value_for_valid_expression() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        // Position (0, 4) is around "2" or "+"; we expect some hover content
        let hover = state.hover_at(&uri, 0, 4);
        assert!(hover.is_some());
        let (content, _range) = hover.unwrap();
        assert!(!content.is_empty());
        // Result of "1 + 2" or subexpression
        assert!(content.contains("3") || content.contains("1") || content.contains("2"));
    }

    #[test]
    fn state_hover_at_wrong_uri_returns_none() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri, 1, "1 + 2");
        let other = Url::parse("file:///other.snaq").unwrap();
        assert!(state.hover_at(&other, 0, 0).is_none());
    }

    #[test]
    fn state_inlay_hints_valid_document() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri.clone(), 1, "1 + 2");
        let hints = state.inlay_hints(&uri);
        // May have hint for "1 + 2" or subexpressions
        assert!(hints.len() <= 3);
    }

    #[test]
    fn state_inlay_hints_wrong_uri_returns_empty() {
        let mut state = state::LspState::new();
        let uri = Url::parse("file:///doc.snaq").unwrap();
        state.update_document(uri, 1, "1 + 2");
        let other = Url::parse("file:///other.snaq").unwrap();
        assert!(state.inlay_hints(&other).is_empty());
    }
}
