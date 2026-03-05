/**
 * Stub for monaco-editor in tests. Used by apply-diagnostics.test.ts so dynamic import resolves.
 */
import { vi } from 'vitest'

export const setModelMarkersMock = vi.fn()
export const editor = {
  setModelMarkers: setModelMarkersMock,
}
