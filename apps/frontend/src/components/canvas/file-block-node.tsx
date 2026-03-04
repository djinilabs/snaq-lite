/**
 * File block node: output-only block that holds a URL (blob, data, or https).
 * Display shows a label (filename or "No file"), type (MIME or derived), and URL/location.
 * Single output handle.
 */

import type { CSSProperties } from 'react'
import type { Node, NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { COMPUTATION_OUTPUT_HANDLE_RIGHT } from '~/lib/constants'
import { useGraphStore } from '~/store'
import { NodeContentZone, NodeFrame } from './node-interaction-shell'

const MUTED_STYLE: CSSProperties = { fontSize: 12, color: 'var(--text-muted)' }
const LABEL_STYLE: CSSProperties = { fontWeight: 500, marginRight: 4 }

export type FileBlockData = {
  uri: string
  label?: string
  url?: string
}

type FileFlowNode = Node<FileBlockData, 'file'>

/** Derive display label from file URL. Exported for unit tests. */
export function fileBlockLabel(url: string | undefined): string {
  if (!url) return 'No file'
  try {
    if (url.startsWith('blob:')) {
      return 'File'
    }
    const u = new URL(url)
    const path = u.pathname
    const segment = path.split('/').filter(Boolean).pop()
    return segment ?? 'File'
  } catch {
    return 'File'
  }
}

/** Format MIME type or URL for display as "type" in the file block. Exported for unit tests. */
export function fileBlockTypeLabel(fileType: string | undefined, url: string | undefined): string {
  if (fileType?.trim()) {
    const m = fileType.trim()
    if (m === 'text/csv') return 'CSV'
    if (m === 'text/plain') return 'Plain text'
    if (m.startsWith('text/')) return m
    if (m.startsWith('application/json')) return 'JSON'
    return m
  }
  if (!url) return '—'
  if (url.startsWith('blob:')) return 'Local file'
  if (url.startsWith('data:')) return 'Data URL'
  try {
    const u = new URL(url)
    const path = u.pathname
    const ext = path.split('.').filter(Boolean).pop()?.toLowerCase()
    if (ext === 'csv') return 'CSV'
    if (ext === 'json') return 'JSON'
    if (ext === 'txt') return 'Plain text'
    if (ext) return ext.toUpperCase()
  } catch {
    // ignore
  }
  return 'URL'
}

export function FileBlockNode({ id, data, selected }: NodeProps<FileFlowNode>) {
  const node = useGraphStore((s) => s.nodes.find((n) => n.id === id))
  const url = node?.type === 'file' ? node.url : data.url
  const fileType = node?.type === 'file' ? node.fileType : undefined
  const label = data.label ?? fileBlockLabel(url)
  const typeLabel = fileBlockTypeLabel(fileType, url)

  return (
    <NodeFrame
      kind="file"
      nodeTestId="file-node"
      titleTestId="file-drag-zone"
      title={label}
      selected={selected}
      minHeight={80}
      nodeId={id}
    >
      <NodeContentZone data-testid="file-content">
        {url ? (
          <dl
            style={{
              margin: 0,
              display: 'flex',
              flexDirection: 'column',
              gap: 6,
              ...MUTED_STYLE,
            }}
          >
            <div style={{ display: 'flex', flexWrap: 'wrap', alignItems: 'baseline' }}>
              <dt style={{ margin: 0, ...LABEL_STYLE }}>Type:</dt>
              <dd style={{ margin: 0 }} data-testid="file-type" title={fileType || undefined}>
                {typeLabel}
              </dd>
            </div>
            <div style={{ display: 'flex', flexWrap: 'wrap', alignItems: 'baseline' }}>
              <dt style={{ margin: 0, ...LABEL_STYLE }}>URL:</dt>
              <dd
                style={{ margin: 0, wordBreak: 'break-all' }}
                data-testid="file-url"
                title={url}
              >
                {url.startsWith('blob:') ? 'Local file (blob)' : url.length > 50 ? `${url.slice(0, 47)}…` : url}
              </dd>
            </div>
          </dl>
        ) : (
          <span style={MUTED_STYLE}>Drop a file or add URL</span>
        )}
      </NodeContentZone>
      <Handle
        type="source"
        position={Position.Right}
        id={COMPUTATION_OUTPUT_HANDLE_RIGHT}
        data-testid="file-output-handle"
      />
    </NodeFrame>
  )
}
