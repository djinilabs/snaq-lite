/**
 * Presentation Block node: placeholder for chart/grid. Subscribes on mount (subscribeWidget),
 * unsubscribes on unmount (unsubscribeWidget); consumes widgetDataUpdate for this widgetId.
 * Sends didOpen for this node's URI so LSP has the target document open for graph_connect when wiring.
 */

import { useEffect } from 'react'
import type { Node, NodeProps } from '@xyflow/react'
import { Handle, Position } from '@xyflow/react'
import { DEFAULT_PRESENTATION_DOCUMENT_CONTENT, LSP_METHOD_DID_OPEN } from '~/lib/constants'
import { hasLanguageClient, getLanguageClient } from '~/lsp/language-client-singleton'
import { useGraphStore } from '~/store'
import { PresentationBlock } from '~/components/presentation/presentation-block'
import { NodeContentZone, NodeFrame } from './node-interaction-shell'

export type PresentationBlockData = {
  uri: string
  sourceUri: string
  label?: string
}

type PresentationFlowNode = Node<PresentationBlockData, 'presentation'>

function presentationDocumentContent(inputs: { name: string; type: string }[] | undefined): string {
  if (!inputs?.length) return DEFAULT_PRESENTATION_DOCUMENT_CONTENT
  return inputs.map((i) => `input ${i.name}: ${i.type}\n$${i.name}`).join('\n')
}

export function PresentationBlockNode({
  id,
  data,
  selected,
}: NodeProps<PresentationFlowNode>) {
  const node = useGraphStore((s) => s.nodes.find((n) => n.id === id))

  useEffect(() => {
    if (!hasLanguageClient()) return
    const content = presentationDocumentContent(node?.inputs)
    getLanguageClient().sendNotification(LSP_METHOD_DID_OPEN, {
      textDocument: { uri: data.uri, version: 1, languageId: 'snaq', text: content },
    })
  }, [data.uri, node?.inputs])

  return (
    <NodeFrame
      kind="presentation"
      nodeTestId="presentation-node"
      titleTestId="presentation-drag-zone"
      title={data.label ?? 'Presentation'}
      selected={selected}
      minHeight={120}
    >
      <Handle type="target" position={Position.Left} id="x" data-testid="presentation-input-handle" />
      <NodeContentZone data-testid="presentation-content">
        <PresentationBlock sourceUri={data.sourceUri} documentUri={data.uri} />
      </NodeContentZone>
    </NodeFrame>
  )
}
