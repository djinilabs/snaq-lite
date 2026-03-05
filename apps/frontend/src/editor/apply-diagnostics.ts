/**
 * Applies LSP textDocument/publishDiagnostics to Monaco editor markers.
 * Used as the onPublishDiagnostics handler so route-message does not import monaco-editor.
 * When the model does not exist yet (e.g. editor not mounted), diagnostics are stored and
 * applied when the model is created (flushPendingDiagnosticsForUri is registered via setOnModelCreated).
 */

import type { PublishDiagnosticsParams } from '~/lsp'
import { ensureMonacoEnvironment } from '~/monaco-environment'
import { getModel, setOnModelCreated, setOnModelDisposed } from './text-model-registry'
import { DIAGNOSTICS_SOURCE, lspDiagnosticToMarker } from './diagnostics-mapping'

/** Pending diagnostics per URI when the model is not yet in the registry. */
const pendingByUri = new Map<
  string,
  { diagnostics: NonNullable<PublishDiagnosticsParams['diagnostics']> }
>()

/**
 * Normalizes LSP URI to a string for model lookup (handles string or object with toString).
 */
function normalizeUri(uri: unknown): string {
  if (typeof uri === 'string') return uri
  if (
    uri &&
    typeof uri === 'object' &&
    'toString' in uri &&
    typeof (uri as { toString: () => string }).toString === 'function'
  ) {
    return (uri as { toString: () => string }).toString()
  }
  return ''
}

function applyToModel(
  uri: string,
  diagnostics: NonNullable<PublishDiagnosticsParams['diagnostics']>,
  monaco: typeof import('monaco-editor'),
): void {
  const model = getModel(uri, monaco)
  if (!model) return
  const markers = diagnostics.map((d) => lspDiagnosticToMarker(d))
  monaco.editor.setModelMarkers(model, DIAGNOSTICS_SOURCE, markers)
  pendingByUri.delete(uri)
}

export function applyDiagnosticsToMonaco(params: PublishDiagnosticsParams): void {
  const uriString = normalizeUri(params?.uri)
  const diagnostics = params?.diagnostics
  if (!uriString || !Array.isArray(diagnostics)) return
  ensureMonacoEnvironment()
  void import('monaco-editor').then((monaco) => {
    const model = getModel(uriString, monaco)
    if (model) {
      applyToModel(uriString, diagnostics, monaco)
    } else {
      pendingByUri.set(uriString, { diagnostics })
    }
  })
}

/** Called from text-model-registry when a model is created; applies any pending diagnostics for that URI. */
export function flushPendingDiagnosticsForUri(uri: string): void {
  const pending = pendingByUri.get(uri)
  if (!pending) return
  ensureMonacoEnvironment()
  void import('monaco-editor').then((monaco) => {
    applyToModel(uri, pending.diagnostics, monaco)
  })
}

function clearPendingForUri(uri: string): void {
  pendingByUri.delete(uri)
}

setOnModelCreated(flushPendingDiagnosticsForUri)
setOnModelDisposed(clearPendingForUri)
