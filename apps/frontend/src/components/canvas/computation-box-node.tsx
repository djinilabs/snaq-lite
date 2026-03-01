/**
 * Computation Box node: title, position, Monaco container, input/output anchors from store.
 * Uses ResizeObserver for editor dimensions and IntersectionObserver to mount the editor
 * only when in view (placeholder when not).
 */

import { useState, useEffect, useRef } from 'react'
import type { NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { useGraphStore } from '~/store'
import { ComputationBoxEditor } from '~/components/editor/computation-box-editor'
import {
  computationNodeHandleTop,
  computationNodeMinHeight,
} from './computation-box-layout'

export type ComputationBoxData = {
  uri: string
  label?: string
}

const PLACEHOLDER_MIN_HEIGHT = 60

export function ComputationBoxNode({ id, data }: NodeProps<{ data: ComputationBoxData }>) {
  const nodes = useGraphStore((s) => s.nodes)
  const node = nodes.find((n) => n.id === id)
  const inputs = node?.inputs ?? []

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
      { threshold: 0.1, rootMargin: '50px' },
    )
    io.observe(el)
    return () => io.disconnect()
  }, [])

  const visible = inView

  return (
    <div
      data-testid="computation-node"
      style={{
        background: '#2d2d44',
        border: '1px solid #444',
        borderRadius: 8,
        minWidth: 240,
        minHeight,
        padding: 8,
      }}
    >
      <div style={{ fontSize: 11, color: '#888', marginBottom: 4 }}>
        {data.label ?? 'Computation'}
      </div>
      {inputs.map((inp, i) => (
        <Handle
          key={inp.name}
          type="target"
          position={Position.Left}
          id={inp.name}
          style={{ top: computationNodeHandleTop(i) }}
        />
      ))}
      <Handle type="source" position={Position.Right} id="output" />
      <div
        ref={editorWrapRef}
        style={{
          width: '100%',
          minHeight: PLACEHOLDER_MIN_HEIGHT,
          position: 'relative',
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
              background: '#1e1e2e',
              borderRadius: 4,
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
              color: '#666',
              fontSize: 12,
            }}
          >
            …
          </div>
        )}
      </div>
    </div>
  )
}
