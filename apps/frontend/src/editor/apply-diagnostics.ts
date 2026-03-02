/**
 * Applies LSP textDocument/publishDiagnostics to Monaco editor markers.
 * Used as the onPublishDiagnostics handler so route-message does not import monaco-editor.
 */

import type { PublishDiagnosticsParams } from '~/lsp'
import { ensureMonacoEnvironment } from '~/monaco-environment'
import { getModel } from './text-model-registry'
import { DIAGNOSTICS_SOURCE, lspDiagnosticToMarker } from './diagnostics-mapping'

export function applyDiagnosticsToMonaco(params: PublishDiagnosticsParams): void {
  const uri = params?.uri
  const diagnostics = params?.diagnostics
  if (typeof uri !== 'string' || !Array.isArray(diagnostics)) return
  ensureMonacoEnvironment()
  void import('monaco-editor').then((monaco) => {
    const model = getModel(uri, monaco)
    if (!model) return
    const markers = diagnostics.map((d) => lspDiagnosticToMarker(d))
    monaco.editor.setModelMarkers(model, DIAGNOSTICS_SOURCE, markers)
  })
}
