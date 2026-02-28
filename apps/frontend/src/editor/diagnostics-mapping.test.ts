import { describe, it, expect } from 'vitest'
import {
  DIAGNOSTICS_SOURCE,
  lspSeverityToMonaco,
  lspDiagnosticToMarker,
} from './diagnostics-mapping'

describe('diagnostics-mapping', () => {
  describe('DIAGNOSTICS_SOURCE', () => {
    it('is snaq-lite for setModelMarkers source', () => {
      expect(DIAGNOSTICS_SOURCE).toBe('snaq-lite')
    })
  })

  describe('lspSeverityToMonaco', () => {
    it('maps LSP 1 (Error) to Monaco 8', () => {
      expect(lspSeverityToMonaco(1)).toBe(8)
    })
    it('maps LSP 2 (Warning) to Monaco 4', () => {
      expect(lspSeverityToMonaco(2)).toBe(4)
    })
    it('maps LSP 3 (Information) to Monaco 2', () => {
      expect(lspSeverityToMonaco(3)).toBe(2)
    })
    it('maps LSP 4 (Hint) to Monaco 1', () => {
      expect(lspSeverityToMonaco(4)).toBe(1)
    })
    it('maps undefined or unknown to Monaco 8 (Error)', () => {
      expect(lspSeverityToMonaco(undefined)).toBe(8)
      expect(lspSeverityToMonaco(99)).toBe(8)
    })
  })

  describe('lspDiagnosticToMarker', () => {
    it('converts 0-based LSP range to 1-based Monaco marker', () => {
      const marker = lspDiagnosticToMarker({
        range: { start: { line: 0, character: 3 }, end: { line: 1, character: 0 } },
        message: 'parse error',
        severity: 1,
      })
      expect(marker).toEqual({
        startLineNumber: 1,
        startColumn: 4,
        endLineNumber: 2,
        endColumn: 1,
        message: 'parse error',
        severity: 8,
      })
    })

    it('uses defaults for missing range and message', () => {
      const marker = lspDiagnosticToMarker({})
      expect(marker).toEqual({
        startLineNumber: 1,
        startColumn: 1,
        endLineNumber: 1,
        endColumn: 1,
        message: '',
        severity: 8,
      })
    })

    it('maps severity through lspSeverityToMonaco', () => {
      expect(lspDiagnosticToMarker({ severity: 2 }).severity).toBe(4)
      expect(lspDiagnosticToMarker({ severity: 4 }).severity).toBe(1)
    })
  })
})
