/**
 * Presentation Block node: placeholder for chart/grid. Subscribes on mount (subscribeWidget),
 * unsubscribes on unmount (unsubscribeWidget); consumes widgetDataUpdate for this widgetId.
 */

import type { NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { DRAG_HANDLE_CLASS_PRESENTATION, NODRAG_CLASS } from '~/lib/constants'
import { PresentationBlock } from '~/components/presentation/presentation-block'

export type PresentationBlockData = {
  uri: string
  sourceUri: string
  label?: string
}

export function PresentationBlockNode({
  data,
  selected,
}: NodeProps<{ data: PresentationBlockData }>) {
  return (
    <div
      className="nopan"
      data-testid="presentation-node"
      style={{
        background: 'var(--bg-card)',
        border: '1px solid var(--border)',
        borderRadius: 'var(--radius)',
        minWidth: 260,
        minHeight: 120,
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
        className={DRAG_HANDLE_CLASS_PRESENTATION}
        style={{
          fontSize: 12,
          color: 'var(--text-muted)',
          marginBottom: 8,
          fontWeight: 500,
          cursor: 'grab',
        }}
      >
        {data.label ?? 'Presentation'}
      </div>
      <Handle type="target" position={Position.Left} id="input" />
      <div
        className={NODRAG_CLASS}
        onPointerDown={(e) => e.stopPropagation()}
        onMouseDown={(e) => e.stopPropagation()}
      >
        <PresentationBlock sourceUri={data.sourceUri} />
      </div>
    </div>
  )
}
