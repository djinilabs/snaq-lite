/**
 * Renders Monaco when node is in view or focused; creates/gets model via virtual-uri;
 * calls layout() on resize; didChange is sent via LSP (message router).
 */

import { useEffect, useRef } from 'react'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { getOrCreateModel, disposeModel } from '~/editor/text-model-registry'
import { sendNotification } from '~/lsp'

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

  const uri = nodeIdToUri(nodeId)

  useEffect(() => {
    if (!visible || !containerRef.current) return
    import('monaco-editor').then((monaco) => {
      try {
        monaco.languages.register({ id: 'snaq' })
      } catch {
        // already registered
      }
      const model = getOrCreateModel(uri, monaco, initialContent)
      const editor = monaco.editor.create(containerRef.current!, {
        model,
        minimap: { enabled: false },
        scrollBeyondLastLine: false,
        language: 'snaq',
      })
      editorRef.current = editor
      sendNotification(LSP_METHOD_DID_OPEN, {
        textDocument: { uri, version: 1, languageId: 'snaq', text: model.getValue() },
      })
      model.onDidChangeContent(() => {
        sendNotification(LSP_METHOD_DID_CHANGE, {
          textDocument: { uri, version: model.getVersionId() },
          contentChanges: [{ text: model.getValue() }],
        })
      })
    })
    return () => {
      editorRef.current?.dispose()
      editorRef.current = null
      disposeModel(uri)
    }
  }, [uri, visible, initialContent])

  useEffect(() => {
    if (editorRef.current) editorRef.current.layout({ width, height })
  }, [width, height])

  if (!visible) return null
  return <div ref={containerRef} style={{ width, height, minHeight: 60 }} />
}
