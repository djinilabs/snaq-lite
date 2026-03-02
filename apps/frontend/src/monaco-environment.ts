/**
 * Configures Monaco to use web workers so editor work runs off the main thread.
 * Call ensureMonacoEnvironment() synchronously before any dynamic import('monaco-editor').
 * See https://github.com/microsoft/monaco-editor#faq and integrate-esm.md (Vite + getWorker).
 */
/// <reference types="vite/client" />

import EditorWorker from 'monaco-editor/esm/vs/editor/editor.worker.js?worker'

declare global {
  interface Window {
    MonacoEnvironment?: {
      getWorker?(workerId: string, label: string): Worker
    }
  }
}

const getWorker = (_workerId: string, _label: string): Worker => {
  return new EditorWorker()
}

export function ensureMonacoEnvironment(): void {
  if (typeof self !== 'undefined' && !self.MonacoEnvironment) {
    self.MonacoEnvironment = { getWorker }
  }
}

// Set as soon as this module loads (e.g. from entry-client) so it's ready if chunk order is correct.
ensureMonacoEnvironment()
