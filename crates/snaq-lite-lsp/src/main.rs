//! Native entry point: run the LSP server on stdin/stdout with Tokio.

#[cfg(not(target_arch = "wasm32"))]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    snaq_lite_lsp::run_native(stdin, stdout).await
}

#[cfg(target_arch = "wasm32")]
fn main() {
    eprintln!("snaq-lite-lsp binary is for native only; use the WASM library and start_snaq_lite_lsp() in a Web Worker.");
    std::process::abort();
}
