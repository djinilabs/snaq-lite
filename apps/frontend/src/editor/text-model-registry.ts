/**
 * Map URI → Monaco ITextModel. Create/get model for a node URI, dispose on node remove.
 * Used by computation-box-editor to bind each box to a virtual document.
 */

import type * as Monaco from 'monaco-editor'
import { nodeIdToUri } from './virtual-uri'

const models = new Map<string, Monaco.editor.ITextModel>()

/** Called when a new model is first created (not when returning an existing one). Used to apply pending diagnostics. */
let onModelCreated: ((uri: string) => void) | null = null
/** Called when a model is disposed so consumers can clear related state (e.g. pending diagnostics). */
let onModelDisposed: ((uri: string) => void) | null = null

export function setOnModelCreated(fn: (uri: string) => void): void {
  onModelCreated = fn
}

export function setOnModelDisposed(fn: (uri: string) => void): void {
  onModelDisposed = fn
}

export function getModel(uri: string, _monaco: typeof import('monaco-editor')): Monaco.editor.ITextModel | null {
  return models.get(uri) ?? null
}

export function getOrCreateModel(
  uri: string,
  monaco: typeof import('monaco-editor'),
  initialValue = '',
): Monaco.editor.ITextModel {
  let model = models.get(uri)
  if (model) return model
  model = monaco.editor.createModel(initialValue, 'snaq', monaco.Uri.parse(uri))
  models.set(uri, model)
  onModelCreated?.(uri)
  return model
}

export function disposeModel(uri: string): void {
  const model = models.get(uri)
  if (model) {
    model.dispose()
    models.delete(uri)
    onModelDisposed?.(uri)
  }
}

export function hasModel(uri: string): boolean {
  return models.has(uri)
}

/** Dispose all models for the given node IDs (e.g. on project switch). */
export function disposeAllGraphModels(nodeIds: string[]): void {
  for (const id of nodeIds) {
    disposeModel(nodeIdToUri(id))
  }
}
