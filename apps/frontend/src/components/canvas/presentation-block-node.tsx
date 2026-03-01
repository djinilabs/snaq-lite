/**
 * Presentation Block node: placeholder for chart/grid. Subscribes on mount (subscribeWidget),
 * unsubscribes on unmount (unsubscribeWidget); consumes widgetDataUpdate for this widgetId.
 */

import type { Node, NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { PresentationBlock } from '~/components/presentation/presentation-block'
import { NodeContentZone, NodeFrame } from './node-interaction-shell'

export type PresentationBlockData = {
  uri: string
  sourceUri: string
  label?: string
}

type PresentationFlowNode = Node<PresentationBlockData, 'presentation'>

export function PresentationBlockNode({
  data,
  selected,
}: NodeProps<PresentationFlowNode>) {
  return (
    <NodeFrame
      kind="presentation"
      nodeTestId="presentation-node"
      titleTestId="presentation-drag-zone"
      title={data.label ?? 'Presentation'}
      selected={selected}
      minHeight={120}
    >
      <Handle type="target" position={Position.Left} id="input" />
      <NodeContentZone data-testid="presentation-content">
        <PresentationBlock sourceUri={data.sourceUri} />
      </NodeContentZone>
    </NodeFrame>
  )
}
