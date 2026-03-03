/**
 * Renders Monaco when node is in view or focused; creates/gets model via virtual-uri;
 * calls layout() on resize. Sends didOpen/didChange via the language client when available.
 * On unmount disposes only the editor instance; the model stays in the registry (disposed when node is removed from graph).
 * Uses a run-id guard so only one editor is created if the effect re-runs before the async import resolves (e.g. Strict Mode).
 */

import type { RefObject } from 'react'
import { useEffect, useLayoutEffect, useRef, useState } from 'react'
import { useAutoSave } from '~/contexts/auto-save-context'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { getOrCreateModel } from '~/editor/text-model-registry'
import { ensureMonacoEnvironment } from '~/monaco-environment'
import { buildComputationDocumentContent } from '~/lib/computation-document-content'
import { LSP_METHOD_DID_OPEN, LSP_METHOD_DID_CHANGE } from '~/lib/constants'
import { hasLanguageClient, getLanguageClient } from '~/lsp/language-client-singleton'
import { useGraphStore } from '~/store'
import { focusDebugEditorFocusLost, focusDebugEditorRender } from '~/lib/focus-debug'

interface ComputationBoxEditorProps {
  nodeId: string
  visible?: boolean
  /** When provided, editor observes this for size and does not require width/height from parent (avoids parent re-renders on resize). */
  wrapperRef?: RefObject<HTMLDivElement | null>
  width?: number
  height?: number
  initialContent?: string
  /** Called when the user edits content (used to trigger re-subscribe for result). */
  onContentChange?: () => void
  /** Called when the editor loses focus (e.g. to flush content to store before connecting). */
  onBlur?: () => void
}

const DEFAULT_WIDTH = 224
const DEFAULT_HEIGHT = 80

export function ComputationBoxEditor({
  nodeId,
  visible = true,
  wrapperRef,
  width: widthProp,
  height: heightProp,
  initialContent = '',
  onContentChange,
  onBlur: onBlurProp,
}: ComputationBoxEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null)
  const editorRef = useRef<import('monaco-editor').editor.IStandaloneCodeEditor | null>(null)
  const effectRunIdRef = useRef(0)
  /** Timestamp when the editor last had focus; used to restore focus after re-render-induced loss (focusout can fire before useLayoutEffect, so a boolean would be cleared too early). */
  const hadFocusAtRef = useRef<number>(0)
  const [observedSize, setObservedSize] = useState({ width: DEFAULT_WIDTH, height: DEFAULT_HEIGHT })
  const width = widthProp ?? observedSize.width
  const height = heightProp ?? observedSize.height
  const autoSave = useAutoSave()
  const requestSaveRef = useRef(autoSave?.requestSave ?? (() => {}))
  requestSaveRef.current = autoSave?.requestSave ?? (() => {})
  const onContentChangeRef = useRef(onContentChange)
  onContentChangeRef.current = onContentChange
  const onBlurRef = useRef(onBlurProp)
  onBlurRef.current = onBlurProp

  const uri = nodeIdToUri(nodeId)

  useEffect(() => {
    if (!visible || !containerRef.current) return
    ensureMonacoEnvironment()
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
        lineNumbers: 'off',
        lineNumbersMinChars: 0,
        glyphMargin: false,
        folding: false,
        lineDecorationsWidth: 0,
        minimap: { enabled: false },
        overviewRulerLanes: 0,
        overviewRulerBorder: false,
        scrollbar: { vertical: 'hidden' },
        scrollBeyondLastLine: false,
        language: 'snaq',
      })
      editor.updateOptions({ minimap: { enabled: false } })
      if (runId !== effectRunIdRef.current) {
        editor.dispose()
        return
      }
      editorRef.current = editor
      const container = editor.getContainerDomNode()
      const onFocusIn = () => {
        hadFocusAtRef.current = Date.now()
      }
      const onFocusOut = (e: FocusEvent) => {
        focusDebugEditorFocusLost(nodeId, document.activeElement ?? undefined, e.relatedTarget)
        onBlurRef.current?.()
      }
      container.addEventListener('focusin', onFocusIn)
      container.addEventListener('focusout', onFocusOut)
      editor.onDidDispose(() => {
        container.removeEventListener('focusin', onFocusIn)
        container.removeEventListener('focusout', onFocusOut)
      })
      if (useGraphStore.getState().focusEditorForNodeId === nodeId) {
        editor.focus()
        useGraphStore.getState().setFocusEditorForNodeId(null)
      }
      if (hasLanguageClient()) {
        const node = useGraphStore.getState().nodes.find((n) => n.id === nodeId)
        const body = model.getValue()
        const text = buildComputationDocumentContent(body, node?.inputs)
        getLanguageClient().sendNotification(LSP_METHOD_DID_OPEN, {
          textDocument: { uri, version: 1, languageId: 'snaq', text },
        })
      }
      model.onDidChangeContent(() => {
        if (hasLanguageClient()) {
          const node = useGraphStore.getState().nodes.find((n) => n.id === nodeId)
          const body = model.getValue()
          const text = buildComputationDocumentContent(body, node?.inputs)
          getLanguageClient().sendNotification(LSP_METHOD_DID_CHANGE, {
            textDocument: { uri, version: model.getVersionId() },
            contentChanges: [{ text }],
          })
        }
        requestSaveRef.current()
        onContentChangeRef.current?.()
      })
    })
    return () => {
      effectRunIdRef.current = runId + 1
      editorRef.current?.dispose()
      editorRef.current = null
      // Do not dispose the model here; it is disposed when the node is removed from the graph (store subscription).
    }
    // initialContent intentionally omitted: only used for initial model creation; including it would recreate the editor on parent re-renders (e.g. when result updates) and cause focus loss.
    // eslint-disable-next-line react-hooks/exhaustive-deps -- see comment above
  }, [nodeId, uri, visible])

  useEffect(() => {
    if (editorRef.current) editorRef.current.layout({ width, height })
  }, [width, height])

  useEffect(() => {
    if (!wrapperRef?.current) return
    const el = wrapperRef.current
    const ro = new ResizeObserver((entries) => {
      const entry = entries[0]
      if (!entry) return
      const w = Math.max(1, entry.contentRect.width)
      const h = Math.max(1, entry.contentRect.height)
      setObservedSize({ width: w, height: h })
      editorRef.current?.layout({ width: w, height: h })
    })
    ro.observe(el)
    return () => ro.disconnect()
  }, [wrapperRef])

  // Restore focus when it was lost due to parent re-render. Use "had focus within last 200ms" so we
  // still restore when focusout fires before this effect and would have cleared a boolean.
  // Also schedule rAF restore so we catch focus lost to async DOM updates (e.g. after LSP/store updates).
  const FOCUS_RESTORE_WINDOW_MS = 200
  useLayoutEffect(() => {
    if (!editorRef.current || !containerRef.current) return
    if (containerRef.current.contains(document.activeElement)) return
    const now = Date.now()
    if (now - hadFocusAtRef.current > FOCUS_RESTORE_WINDOW_MS) return
    editorRef.current.focus()
    const rafId = requestAnimationFrame(() => {
      if (!editorRef.current || !containerRef.current) return
      if (containerRef.current.contains(document.activeElement)) return
      if (Date.now() - hadFocusAtRef.current > FOCUS_RESTORE_WINDOW_MS) return
      editorRef.current?.focus()
    })
    return () => cancelAnimationFrame(rafId)
  })

  useEffect(() => {
    focusDebugEditorRender(nodeId)
  })

  if (!visible) return null
  return (
    <div
      ref={containerRef}
      className="computation-box-editor-root"
      style={{ width, height, minHeight: 60 }}
    />
  )
}
