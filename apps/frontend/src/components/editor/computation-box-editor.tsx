/**
 * Renders Monaco when node is in view or focused; creates/gets model via virtual-uri;
 * calls layout() on resize. Sends didOpen/didChange via the language client when available.
 * On unmount disposes only the editor instance; the model stays in the registry (disposed when node is removed from graph).
 * Uses a run-id guard so only one editor is created if the effect re-runs before the async import resolves (e.g. Strict Mode).
 */

import { useEffect, useRef } from 'react'
import { useAutoSave } from '~/contexts/auto-save-context'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { getOrCreateModel } from '~/editor/text-model-registry'
import { hasLanguageClient, getLanguageClient } from '~/lsp/language-client-singleton'
import { useGraphStore } from '~/store'

const LSP_METHOD_DID_OPEN = 'textDocument/didOpen'
const LSP_METHOD_DID_CHANGE = 'textDocument/didChange'

interface ComputationBoxEditorProps {
  nodeId: string
  visible?: boolean
  width: number
  height: number
  initialContent?: string
}

export function ComputationBoxEditor({
  nodeId,
  visible = true,
  width,
  height,
  initialContent = '',
}: ComputationBoxEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null)
  const editorRef = useRef<import('monaco-editor').editor.IStandaloneCodeEditor | null>(null)
  const effectRunIdRef = useRef(0)
  const autoSave = useAutoSave()
  const requestSaveRef = useRef(autoSave?.requestSave ?? (() => {}))
  requestSaveRef.current = autoSave?.requestSave ?? (() => {})

  const uri = nodeIdToUri(nodeId)

  useEffect(() => {
    if (!visible || !containerRef.current) return
    const runId = ++effectRunIdRef.current
    import('monaco-editor').then((monaco) => {
      // Only create an editor if this effect run is still current (avoids duplicate editors
      // when the effect re-runs before the import resolves, e.g. React Strict Mode or store updates).
      if (runId !== effectRunIdRef.current) return
      if (!containerRef.current) return
      try {
        monaco.languages.register({ id: 'snaq' })
      } catch {
        // already registered
      }
      const model = getOrCreateModel(uri, monaco, initialContent)
      const editor = monaco.editor.create(containerRef.current, {
        model,
        minimap: { enabled: false },
        scrollBeyondLastLine: false,
        language: 'snaq',
      })
      if (runId !== effectRunIdRef.current) {
        editor.dispose()
        return
      }
      editorRef.current = editor
      if (useGraphStore.getState().focusEditorForNodeId === nodeId) {
        editor.focus()
        useGraphStore.getState().setFocusEditorForNodeId(null)
      }
      if (hasLanguageClient()) {
        getLanguageClient().sendNotification(LSP_METHOD_DID_OPEN, {
          textDocument: { uri, version: 1, languageId: 'snaq', text: model.getValue() },
        })
      }
      model.onDidChangeContent(() => {
        if (hasLanguageClient()) {
          getLanguageClient().sendNotification(LSP_METHOD_DID_CHANGE, {
            textDocument: { uri, version: model.getVersionId() },
            contentChanges: [{ text: model.getValue() }],
          })
        }
        requestSaveRef.current()
      })
    })
    return () => {
      effectRunIdRef.current = runId + 1
      editorRef.current?.dispose()
      editorRef.current = null
      // Do not dispose the model here; it is disposed when the node is removed from the graph (store subscription).
    }
  }, [nodeId, uri, visible, initialContent])

  useEffect(() => {
    if (editorRef.current) editorRef.current.layout({ width, height })
  }, [width, height])

  if (!visible) return null
  return <div ref={containerRef} style={{ width, height, minHeight: 60 }} />
}
