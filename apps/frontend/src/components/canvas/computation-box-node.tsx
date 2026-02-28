/**
 * Computation Box node: title, position, Monaco container, input/output anchors from store.
 */

import type { NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { useGraphStore } from '~/store'
import { ComputationBoxEditor } from '~/components/editor/computation-box-editor'

export type ComputationBoxData = {
  uri: string
  label?: string
}

export function ComputationBoxNode({ id, data }: NodeProps<{ data: ComputationBoxData }>) {
  const nodes = useGraphStore((s) => s.nodes)
  const node = nodes.find((n) => n.id === id)
  const inputs = node?.inputs ?? []

  return (
    <div
      style={{
        background: '#2d2d44',
        border: '1px solid #444',
        borderRadius: 8,
        minWidth: 240,
        minHeight: 120,
        padding: 8,
      }}
    >
      <div style={{ fontSize: 11, color: '#888', marginBottom: 4 }}>
        {data.label ?? 'Computation'}
      </div>
      {inputs.map((inp) => (
        <Handle
          key={inp.name}
          type="target"
          position={Position.Left}
          id={inp.name}
          style={{ top: 'auto', bottom: 8 }}
        />
      ))}
      <Handle type="source" position={Position.Right} id="output" />
      <ComputationBoxEditor nodeId={id} visible width={224} height={80} />
    </div>
  )
}
