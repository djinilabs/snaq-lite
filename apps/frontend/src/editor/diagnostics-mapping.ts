/**
 * Pure mapping from LSP publishDiagnostics to Monaco marker shape.
 * Testable without loading monaco-editor.
 */

export const DIAGNOSTICS_SOURCE = 'snaq-lite'

export function lspSeverityToMonaco(severity: number | undefined): number {
  switch (severity) {
    case 1:
      return 8 // Error
    case 2:
      return 4 // Warning
    case 3:
      return 2 // Information
    case 4:
      return 1 // Hint
    default:
      return 8 // Error
  }
}

export interface LspDiagnosticForMapping {
  range?: {
    start?: { line?: number; character?: number }
    end?: { line?: number; character?: number }
  }
  message?: string
  severity?: number
}

export interface MonacoMarkerShape {
  startLineNumber: number
  startColumn: number
  endLineNumber: number
  endColumn: number
  message: string
  severity: number
}

export function lspDiagnosticToMarker(d: LspDiagnosticForMapping): MonacoMarkerShape {
  return {
    startLineNumber: (d.range?.start?.line ?? 0) + 1,
    startColumn: (d.range?.start?.character ?? 0) + 1,
    endLineNumber: (d.range?.end?.line ?? 0) + 1,
    endColumn: (d.range?.end?.character ?? 0) + 1,
    message: d.message ?? '',
    severity: lspSeverityToMonaco(d.severity),
  }
}
