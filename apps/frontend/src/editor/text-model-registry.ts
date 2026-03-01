/**
 * Map URI → Monaco ITextModel. Create/get model for a node URI, dispose on node remove.
 * Used by computation-box-editor to bind each box to a virtual document.
 */

import type * as Monaco from 'monaco-editor'
import { nodeIdToUri } from './virtual-uri'

const models = new Map<string, Monaco.editor.ITextModel>()

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
  return model
}

export function disposeModel(uri: string): void {
  const model = models.get(uri)
  if (model) {
    model.dispose()
    models.delete(uri)
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
