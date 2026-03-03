/**
 * Computation Box node: title, position, Monaco container, input/output anchors from store.
 * Inputs are block properties editable in the UI (not in block text). Use $name in the script to reference.
 * Subscribes to its own result (subscribeWidget with sourceUri = block URI) and shows result below editor.
 * Uses ResizeObserver for editor dimensions and IntersectionObserver to mount the editor
 * only when in view (placeholder when not).
 */

import { useState, useEffect, useRef, useCallback } from 'react'
import type { Node, NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { getModel } from '~/editor/text-model-registry'
import { INPUT_PORT_TYPES, LSP_METHOD_DID_OPEN } from '~/lib/constants'
import type { NodeInputPort } from '~/lsp/types'
import { useSubscribeWidget } from '~/hooks/use-subscribe-widget'
import { useGraphStore, useWidgetStore } from '~/store'
import { useWidgetContentVersionStore } from '~/store/widget-content-version-store'
import { getLanguageClient } from '~/lsp/language-client-singleton'
import { ComputationBoxEditor } from '~/components/editor/computation-box-editor'
import { WidgetDataView } from '~/components/presentation/widget-data-view'

/** Isolates widget store subscription so parent node does not re-render on result update (preserves editor focus). */
function ComputationResultBlock({ widgetId }: { widgetId: string }) {
  const resultState = useWidgetStore((s) => s.byId[widgetId])
  return (
    <NodeContentZone
      data-testid="computation-result"
      style={{
        marginTop: 10,
        paddingTop: 8,
        borderTop: '1px solid var(--border)',
        fontSize: 12,
      }}
    >
      <div style={{ color: 'var(--text-muted)', marginBottom: 4, fontWeight: 500 }}>
        Result
      </div>
      <WidgetDataView state={resultState} />
    </NodeContentZone>
  )
}

/** Runs useSubscribeWidget with subscribeKey from store so the node does not re-render when content version increments (preserves editor focus). */
function WidgetSubscription({
  widgetId,
  sourceUri,
  onBeforeSubscribe,
}: {
  widgetId: string
  sourceUri: string
  onBeforeSubscribe: () => void
}) {
  const contentVersion = useWidgetContentVersionStore((s) => s.byWidgetId[widgetId] ?? 0)
  useSubscribeWidget({
    widgetId,
    sourceUri,
    enabled: true,
    onBeforeSubscribe,
    subscribeKey: contentVersion,
  })
  return null
}
import { NodeContentZone, NodeFrame } from './node-interaction-shell'
import { focusDebugNodeRender } from '~/lib/focus-debug'
import {
  computationNodeHandleTop,
  computationNodeMinHeight,
} from './computation-box-layout'

export type ComputationBoxData = {
  uri: string
  label?: string
}

type ComputationFlowNode = Node<ComputationBoxData, 'computation'>

const PLACEHOLDER_MIN_HEIGHT = 60
const RESULT_WIDGET_ID_PREFIX = 'computation-result-'
const CONTENT_CHANGE_DEBOUNCE_MS = 300

export function ComputationBoxNode({
  id,
  data,
  selected,
}: NodeProps<ComputationFlowNode>) {
  const nodes = useGraphStore((s) => s.nodes)
  const setNodeInputs = useGraphStore((s) => s.setNodeInputs)
  const setNodeContent = useGraphStore((s) => s.setNodeContent)
  const node = nodes.find((n) => n.id === id)
  const inputs = node?.inputs ?? []
  const widgetId = `${RESULT_WIDGET_ID_PREFIX}${id}`
  const debounceRef = useRef<ReturnType<typeof setTimeout> | null>(null)

  const onBeforeSubscribe = useCallback(() => {
    try {
      const text =
        getModel(data.uri, undefined as never)?.getValue() ?? node?.initialContent ?? ''
      getLanguageClient().sendNotification(LSP_METHOD_DID_OPEN, {
        textDocument: { uri: data.uri, version: 1, languageId: 'snaq', text },
      })
    } catch (e) {
      console.error('[ComputationBoxNode] didOpen before subscribe failed:', e)
    }
  }, [data.uri, node?.initialContent])

  const flushContentToStore = useCallback(() => {
    if (debounceRef.current != null) {
      clearTimeout(debounceRef.current)
      debounceRef.current = null
    }
    const content = getModel(data.uri, undefined as never)?.getValue() ?? ''
    setNodeContent(id, content)
  }, [id, data.uri, setNodeContent])

  const onContentChange = useCallback(() => {
    if (debounceRef.current != null) clearTimeout(debounceRef.current)
    debounceRef.current = setTimeout(() => {
      debounceRef.current = null
      const content = getModel(data.uri, undefined as never)?.getValue() ?? ''
      setNodeContent(id, content)
      useWidgetContentVersionStore.getState().increment(widgetId)
    }, CONTENT_CHANGE_DEBOUNCE_MS)
  }, [widgetId, id, data.uri, setNodeContent])

  useEffect(() => {
    return () => {
      if (debounceRef.current != null) clearTimeout(debounceRef.current)
    }
  }, [])

  const minHeight = computationNodeMinHeight(inputs.length)
  const editorWrapRef = useRef<HTMLDivElement>(null)
  const [inView, setInView] = useState(true)

  useEffect(() => {
    const el = editorWrapRef.current
    if (!el) return
    const io = new IntersectionObserver(
      (entries) => {
        const entry = entries[0]
        if (entry) setInView(entry.isIntersecting)
      },
      { threshold: 0, rootMargin: '300px' },
    )
    io.observe(el)
    return () => io.disconnect()
  }, [])

  const visible = inView

  useEffect(() => {
    if (visible) return
    if (debounceRef.current == null) return
    clearTimeout(debounceRef.current)
    debounceRef.current = null
    const content = getModel(data.uri, undefined as never)?.getValue() ?? ''
    setNodeContent(id, content)
  }, [visible, id, data.uri, setNodeContent])

  useEffect(() => {
    focusDebugNodeRender(id)
  })

  const updateInput = (index: number, patch: Partial<NodeInputPort>) => {
    const next = inputs.slice()
    next[index] = { ...next[index], ...patch }
    setNodeInputs(id, next)
  }
  const addInput = () => {
    setNodeInputs(id, [...inputs, { name: '', type: 'Vector' }])
  }
  const removeInput = (index: number) => {
    setNodeInputs(id, inputs.filter((_, i) => i !== index))
  }

  return (
    <NodeFrame
      kind="computation"
      nodeTestId="computation-node"
      titleTestId="computation-drag-zone"
      title={data.label ?? 'Computation'}
      selected={selected}
      minHeight={minHeight}
    >
      <NodeContentZone
        style={{
          fontSize: 11,
          color: 'var(--text-muted)',
          marginBottom: 6,
          opacity: 0.9,
        }}
        title="Inputs are block properties. Use $name in the script."
      >
        Inputs
      </NodeContentZone>
      <NodeContentZone
        nowheel
        onMouseDown={(e) => e.stopPropagation()}
        onClick={(e) => e.stopPropagation()}
        style={{
          marginBottom: 8,
          display: 'flex',
          flexDirection: 'column',
          gap: 4,
        }}
      >
        {inputs.map((inp, i) => (
          <div
            key={i}
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 6,
            }}
          >
            <input
              type="text"
              value={inp.name}
              onChange={(e) => updateInput(i, { name: e.target.value.trim() || e.target.value })}
              placeholder="name"
              data-testid={`computation-input-name-${i}`}
              style={{
                flex: 1,
                minWidth: 0,
                padding: '2px 6px',
                fontSize: 11,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-primary)',
                color: 'var(--text)',
              }}
            />
            <select
              value={inp.type}
              onChange={(e) => updateInput(i, { type: e.target.value })}
              data-testid={`computation-input-type-${i}`}
              style={{
                padding: '2px 4px',
                fontSize: 11,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-primary)',
                color: 'var(--text)',
              }}
            >
              {INPUT_PORT_TYPES.map((t) => (
                <option key={t} value={t}>
                  {t}
                </option>
              ))}
            </select>
            <button
              type="button"
              onClick={() => removeInput(i)}
              title="Remove input"
              data-testid={`computation-input-remove-${i}`}
              style={{
                padding: '2px 6px',
                fontSize: 11,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-primary)',
                color: 'var(--text-muted)',
                cursor: 'pointer',
              }}
            >
              ×
            </button>
          </div>
        ))}
        <button
          type="button"
          onClick={addInput}
          title="Add input port (use $name in script)"
          data-testid="computation-add-input"
          style={{
            alignSelf: 'flex-start',
            padding: '2px 8px',
            fontSize: 11,
            border: '1px solid var(--border)',
            borderRadius: 'var(--radius-sm)',
            background: 'var(--bg-primary)',
            color: 'var(--text-muted)',
            cursor: 'pointer',
          }}
        >
          + Add input
        </button>
      </NodeContentZone>
      {inputs.map(
        (inp, i) =>
          inp.name ? (
            <Handle
              key={inp.name}
              type="target"
              position={Position.Left}
              id={inp.name}
              data-testid={`computation-input-handle-${inp.name}`}
              style={{ top: computationNodeHandleTop(i) }}
            />
          ) : null,
      )}
      <Handle type="source" position={Position.Right} id="output" data-testid="computation-output-handle" />
      <NodeContentZone
        ref={editorWrapRef}
        nowheel
        data-testid="computation-editor-zone"
        style={{
          width: '100%',
          minHeight: PLACEHOLDER_MIN_HEIGHT,
          position: 'relative',
          cursor: 'text',
        }}
      >
        {visible ? (
          <ComputationBoxEditor
            nodeId={id}
            visible
            wrapperRef={editorWrapRef}
            initialContent={node?.initialContent ?? ''}
            onContentChange={onContentChange}
            onBlur={flushContentToStore}
          />
        ) : (
          <div
            style={{
              width: '100%',
              height: 80,
              minHeight: PLACEHOLDER_MIN_HEIGHT,
              background: 'var(--bg-primary)',
              borderRadius: 'var(--radius-sm)',
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
              color: 'var(--text-muted)',
              fontSize: 12,
            }}
          >
            …
          </div>
        )}
      </NodeContentZone>
      <WidgetSubscription
        widgetId={widgetId}
        sourceUri={data.uri}
        onBeforeSubscribe={onBeforeSubscribe}
      />
      <ComputationResultBlock widgetId={widgetId} />
    </NodeFrame>
  )
}
