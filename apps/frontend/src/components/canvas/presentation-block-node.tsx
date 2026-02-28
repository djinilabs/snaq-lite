/**
 * Presentation Block node: placeholder for chart/grid. Subscribes on mount (subscribeWidget),
 * unsubscribes on unmount (unsubscribeWidget); consumes widgetDataUpdate for this widgetId.
 */

import type { NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { PresentationBlock } from '~/components/presentation/presentation-block'

export type PresentationBlockData = {
  uri: string
  sourceUri: string
  label?: string
}

export function PresentationBlockNode({ data }: NodeProps<{ data: PresentationBlockData }>) {
  return (
    <div
      style={{
        background: '#1e2d2e',
        border: '1px solid #355',
        borderRadius: 8,
        minWidth: 240,
        minHeight: 120,
        padding: 8,
      }}
    >
      <div style={{ fontSize: 11, color: '#6a8' }}>{data.label ?? 'Presentation'}</div>
      <Handle type="target" position={Position.Left} id="input" />
      <PresentationBlock sourceUri={data.sourceUri} />
    </div>
  )
}
