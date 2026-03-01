/**
 * Computation Box node: title, position, Monaco container, input/output anchors from store.
 * Inputs are block properties editable in the UI (not in block text). Use $name in the script to reference.
 * Subscribes to its own result (subscribeWidget with sourceUri = block URI) and shows result below editor.
 * Uses ResizeObserver for editor dimensions and IntersectionObserver to mount the editor
 * only when in view (placeholder when not).
 */

import { useState, useEffect, useRef } from 'react'
import type { NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import {
  DRAG_HANDLE_CLASS_COMPUTATION,
  INPUT_PORT_TYPES,
  NODRAG_CLASS,
} from '~/lib/constants'
import type { NodeInputPort } from '~/lsp/types'
import { useSubscribeWidget } from '~/hooks/use-subscribe-widget'
import { useGraphStore, useWidgetStore } from '~/store'
import { ComputationBoxEditor } from '~/components/editor/computation-box-editor'
import { WidgetDataView } from '~/components/presentation/widget-data-view'
import {
  computationNodeHandleTop,
  computationNodeMinHeight,
} from './computation-box-layout'

export type ComputationBoxData = {
  uri: string
  label?: string
}

const PLACEHOLDER_MIN_HEIGHT = 60
const RESULT_WIDGET_ID_PREFIX = 'computation-result-'

export function ComputationBoxNode({
  id,
  data,
  selected,
}: NodeProps<{ data: ComputationBoxData }>) {
  const nodes = useGraphStore((s) => s.nodes)
  const setNodeInputs = useGraphStore((s) => s.setNodeInputs)
  const node = nodes.find((n) => n.id === id)
  const inputs = node?.inputs ?? []
  const widgetId = `${RESULT_WIDGET_ID_PREFIX}${id}`
  const resultState = useWidgetStore((s) => s.byId[widgetId])

  useSubscribeWidget({ widgetId, sourceUri: data.uri, enabled: true })

  const minHeight = computationNodeMinHeight(inputs.length)
  const editorWrapRef = useRef<HTMLDivElement>(null)
  const [editorSize, setEditorSize] = useState({ width: 224, height: 80 })
  const [inView, setInView] = useState(true)

  useEffect(() => {
    const el = editorWrapRef.current
    if (!el) return
    const ro = new ResizeObserver((entries) => {
      const entry = entries[0]
      if (!entry) return
      const { width, height } = entry.contentRect
      setEditorSize({ width: Math.max(1, width), height: Math.max(1, height) })
    })
    ro.observe(el)
    return () => ro.disconnect()
  }, [])

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
    <div
      className="nopan"
      data-testid="computation-node"
      style={{
        background: 'var(--bg-card)',
        border: '1px solid var(--border)',
        borderRadius: 'var(--radius)',
        minWidth: 260,
        minHeight,
        padding: 12,
        boxShadow: 'var(--shadow)',
        cursor: 'default',
        ...(selected && {
          outline: '2px solid var(--accent)',
          outlineOffset: 2,
        }),
      }}
    >
      <div
        className={DRAG_HANDLE_CLASS_COMPUTATION}
        style={{
          fontSize: 12,
          color: 'var(--text-muted)',
          marginBottom: 8,
          fontWeight: 500,
          cursor: 'grab',
        }}
        title="Drag to move the block"
      >
        {data.label ?? 'Computation'}
      </div>
      <div
        className={NODRAG_CLASS}
        onPointerDown={(e) => e.stopPropagation()}
        onMouseDown={(e) => e.stopPropagation()}
        style={{
          fontSize: 11,
          color: 'var(--text-muted)',
          marginBottom: 6,
          opacity: 0.9,
        }}
        title="Inputs are block properties. Use $name in the script."
      >
        Inputs
      </div>
      <div
        className={`${NODRAG_CLASS} nowheel`}
        onPointerDown={(e) => e.stopPropagation()}
        onMouseDown={(e) => e.stopPropagation()}
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
      </div>
      {inputs.map(
        (inp, i) =>
          inp.name ? (
            <Handle
              key={inp.name}
              type="target"
              position={Position.Left}
              id={inp.name}
              style={{ top: computationNodeHandleTop(i) }}
            />
          ) : null,
      )}
      <Handle type="source" position={Position.Right} id="output" />
      <div
        ref={editorWrapRef}
        className={`${NODRAG_CLASS} nowheel`}
        onPointerDown={(e) => e.stopPropagation()}
        onMouseDown={(e) => e.stopPropagation()}
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
            width={editorSize.width}
            height={editorSize.height}
            initialContent={node?.initialContent ?? ''}
          />
        ) : (
          <div
            style={{
              width: '100%',
              height: editorSize.height,
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
      </div>
      <div
        className={NODRAG_CLASS}
        data-testid="computation-result"
        onPointerDown={(e) => e.stopPropagation()}
        onMouseDown={(e) => e.stopPropagation()}
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
      </div>
    </div>
  )
}
