/**
 * Unit tests for apply-diagnostics: LSP publishDiagnostics → Monaco markers.
 * Uses vite.config resolve.alias so dynamic import('monaco-editor') resolves to __mocks__/monaco-editor.
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { setModelMarkersMock } from './__mocks__/monaco-editor'
import { applyDiagnosticsToMonaco, flushPendingDiagnosticsForUri } from './apply-diagnostics'
import { DIAGNOSTICS_SOURCE } from './diagnostics-mapping'

const fakeModel = { id: 'fake-model' }
const getModelMock = vi.fn()
vi.mock('./text-model-registry', () => ({
  getModel: (uri: string, _monaco: unknown) => getModelMock(uri, _monaco),
  setOnModelCreated: vi.fn(),
  setOnModelDisposed: vi.fn(),
}))

vi.mock('~/monaco-environment', () => ({
  ensureMonacoEnvironment: vi.fn(),
}))

/** Wait for dynamic import().then() callback to run (microtasks + next tick). */
async function flushAsync(): Promise<void> {
  await new Promise((r) => setTimeout(r, 0))
  await new Promise((r) => setTimeout(r, 0))
}

describe('applyDiagnosticsToMonaco', () => {
  beforeEach(() => {
    setModelMarkersMock.mockClear()
    getModelMock.mockReset()
  })

  afterEach(() => {
    vi.clearAllMocks()
  })

  it('applies one diagnostic with range to model and calls setModelMarkers', async () => {
    getModelMock.mockReturnValue(fakeModel)

    applyDiagnosticsToMonaco({
      uri: 'snaq://graph/node_1.sl',
      diagnostics: [
        {
          range: { start: { line: 0, character: 2 }, end: { line: 0, character: 5 } },
          message: 'unexpected token',
          severity: 1,
        },
      ],
    })

    await flushAsync()

    expect(getModelMock).toHaveBeenCalledWith('snaq://graph/node_1.sl', expect.anything())
    expect(setModelMarkersMock).toHaveBeenCalledTimes(1)
    expect(setModelMarkersMock).toHaveBeenCalledWith(
      fakeModel,
      DIAGNOSTICS_SOURCE,
      [
        {
          startLineNumber: 1,
          startColumn: 3,
          endLineNumber: 1,
          endColumn: 6,
          message: 'unexpected token',
          severity: 8,
        },
      ],
    )
  })

  it('normalizes URI when given as object with toString', async () => {
    getModelMock.mockReturnValue(fakeModel)
    const uriObj = { toString: () => 'snaq://graph/node_2.sl' }

    applyDiagnosticsToMonaco({
      uri: uriObj as unknown as string,
      diagnostics: [{ range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } }, message: 'err', severity: 1 }],
    })

    await flushAsync()

    expect(getModelMock).toHaveBeenCalledWith('snaq://graph/node_2.sl', expect.anything())
    expect(setModelMarkersMock).toHaveBeenCalledWith(fakeModel, DIAGNOSTICS_SOURCE, expect.any(Array))
  })

  it('stores diagnostics in pending when model is not found and applies when flushPendingDiagnosticsForUri is called', async () => {
    getModelMock.mockReturnValue(null)

    applyDiagnosticsToMonaco({
      uri: 'snaq://graph/node_3.sl',
      diagnostics: [{ range: { start: { line: 1, character: 0 }, end: { line: 1, character: 3 } }, message: 'parse error', severity: 1 }],
    })

    await flushAsync()

    expect(setModelMarkersMock).not.toHaveBeenCalled()

    getModelMock.mockReturnValue(fakeModel)
    flushPendingDiagnosticsForUri('snaq://graph/node_3.sl')

    await flushAsync()

    expect(setModelMarkersMock).toHaveBeenCalledTimes(1)
    expect(setModelMarkersMock).toHaveBeenCalledWith(
      fakeModel,
      DIAGNOSTICS_SOURCE,
      [
        {
          startLineNumber: 2,
          startColumn: 1,
          endLineNumber: 2,
          endColumn: 4,
          message: 'parse error',
          severity: 8,
        },
      ],
    )
  })

  it('does nothing when uri is missing or diagnostics is not an array', () => {
    applyDiagnosticsToMonaco({} as Parameters<typeof applyDiagnosticsToMonaco>[0])
    applyDiagnosticsToMonaco({ uri: 'snaq://graph/x.sl' } as Parameters<typeof applyDiagnosticsToMonaco>[0])
    applyDiagnosticsToMonaco({ uri: '', diagnostics: [] } as Parameters<typeof applyDiagnosticsToMonaco>[0])

    expect(getModelMock).not.toHaveBeenCalled()
  })

  it('flushPendingDiagnosticsForUri with no pending for URI does not call setModelMarkers', async () => {
    flushPendingDiagnosticsForUri('snaq://graph/nonexistent.sl')
    await flushAsync()
    expect(setModelMarkersMock).not.toHaveBeenCalled()
  })

  it('does not call getModel when uri is undefined or null', () => {
    applyDiagnosticsToMonaco({ uri: undefined, diagnostics: [{ message: 'x', severity: 1 }] } as Parameters<
      typeof applyDiagnosticsToMonaco
    >[0])
    applyDiagnosticsToMonaco({ uri: null, diagnostics: [{ message: 'x', severity: 1 }] } as Parameters<
      typeof applyDiagnosticsToMonaco
    >[0])
    expect(getModelMock).not.toHaveBeenCalled()
  })

  it('applies multiple diagnostics and passes all markers to setModelMarkers', async () => {
    getModelMock.mockReturnValue(fakeModel)

    applyDiagnosticsToMonaco({
      uri: 'snaq://graph/node_1.sl',
      diagnostics: [
        { range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } }, message: 'first', severity: 1 },
        { range: { start: { line: 1, character: 2 }, end: { line: 1, character: 5 } }, message: 'second', severity: 2 },
      ],
    })

    await flushAsync()

    expect(setModelMarkersMock).toHaveBeenCalledTimes(1)
    expect(setModelMarkersMock).toHaveBeenCalledWith(fakeModel, DIAGNOSTICS_SOURCE, [
      { startLineNumber: 1, startColumn: 1, endLineNumber: 1, endColumn: 2, message: 'first', severity: 8 },
      { startLineNumber: 2, startColumn: 3, endLineNumber: 2, endColumn: 6, message: 'second', severity: 4 },
    ])
  })

  it('applying empty diagnostics array clears markers for that URI', async () => {
    getModelMock.mockReturnValue(fakeModel)

    applyDiagnosticsToMonaco({
      uri: 'snaq://graph/node_1.sl',
      diagnostics: [],
    })

    await flushAsync()

    expect(setModelMarkersMock).toHaveBeenCalledTimes(1)
    expect(setModelMarkersMock).toHaveBeenCalledWith(fakeModel, DIAGNOSTICS_SOURCE, [])
  })

  it('flush when model still null leaves pending; second flush when model exists applies and clears pending', async () => {
    getModelMock.mockReturnValue(null)

    applyDiagnosticsToMonaco({
      uri: 'snaq://graph/node_late.sl',
      diagnostics: [{ range: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } }, message: 'err', severity: 1 }],
    })
    await flushAsync()
    expect(setModelMarkersMock).not.toHaveBeenCalled()

    flushPendingDiagnosticsForUri('snaq://graph/node_late.sl')
    await flushAsync()
    expect(setModelMarkersMock).not.toHaveBeenCalled()

    getModelMock.mockReturnValue(fakeModel)
    flushPendingDiagnosticsForUri('snaq://graph/node_late.sl')
    await flushAsync()
    expect(setModelMarkersMock).toHaveBeenCalledTimes(1)
    expect(setModelMarkersMock).toHaveBeenCalledWith(fakeModel, DIAGNOSTICS_SOURCE, [
      expect.objectContaining({ message: 'err', startLineNumber: 1, startColumn: 1 }),
    ])
  })
})
