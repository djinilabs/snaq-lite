/**
 * File block node: output-only block that holds a URL (blob, data, or https).
 * Display shows a label (filename or "No file"); URL can be hidden. Single output handle.
 */

import type { Node, NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { COMPUTATION_OUTPUT_HANDLE_RIGHT } from '~/lib/constants'
import { useGraphStore } from '~/store'
import { NodeContentZone, NodeFrame } from './node-interaction-shell'

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

export function FileBlockNode({ id, data, selected }: NodeProps<FileFlowNode>) {
  const node = useGraphStore((s) => s.nodes.find((n) => n.id === id))
  const url = node?.type === 'file' ? node.url : data.url
  const label = data.label ?? fileBlockLabel(url)

  return (
    <NodeFrame
      kind="file"
      nodeTestId="file-node"
      titleTestId="file-drag-zone"
      title={label}
      selected={selected}
      minHeight={80}
    >
      <NodeContentZone data-testid="file-content">
        {url ? (
          <span style={{ fontSize: 12, color: 'var(--text-muted)' }} title={url}>
            {url.startsWith('blob:') ? 'Local file' : url.length > 40 ? `${url.slice(0, 37)}…` : url}
          </span>
        ) : (
          <span style={{ fontSize: 12, color: 'var(--text-muted)' }}>Drop a file or add URL</span>
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
