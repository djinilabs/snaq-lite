/**
 * React Flow wrapper: reads nodes/edges from graph store, custom node types (computation, presentation),
 * handles edge creation (optimistic + snaqlite/graph/connect; on error clear pending + toast).
 */

import { useCallback, useMemo } from 'react'
import {
  ReactFlow,
  Background,
  Controls,
  type Connection,
  type Node,
  type Edge,
  type NodeChange,
} from '@xyflow/react'
import '@xyflow/react/dist/style.css'
import { useGraphStore } from '~/store'
import { ComputationBoxNode } from './computation-box-node'
import { PresentationBlockNode } from './presentation-block-node'
import { connectEdge } from './edge-handlers'

const nodeTypes = {
  computation: ComputationBoxNode,
  presentation: PresentationBlockNode,
}

function graphNodeToFlowNode(n: import('~/store').GraphNode): Node {
  return {
    id: n.id,
    type: n.type,
    position: n.position,
    data: {
      uri: n.uri,
      label: n.id,
      sourceUri: n.uri,
    },
  }
}

function graphEdgeToFlowEdge(e: import('~/store').GraphEdge): Edge {
  return {
    id: `${e.sourceId}-${e.targetId}-${e.targetInputName}`,
    source: e.sourceId,
    target: e.targetId,
    sourceHandle: 'output',
    targetHandle: e.targetInputName,
  }
}

export function GraphCanvas() {
  const storeNodes = useGraphStore((s) => s.nodes)
  const storeEdges = useGraphStore((s) => s.edges)
  const moveNode = useGraphStore((s) => s.moveNode)

  const nodes = useMemo(
    () => storeNodes.map(graphNodeToFlowNode),
    [storeNodes],
  )
  const edges = useMemo(
    () => storeEdges.map(graphEdgeToFlowEdge),
    [storeEdges],
  )

  const onConnect = useCallback(
    async (connection: Connection) => {
      if (!connection.source || !connection.target || !connection.targetHandle) return
      const sourceNode = useGraphStore.getState().nodes.find((n) => n.id === connection.source)
      const targetNode = useGraphStore.getState().nodes.find((n) => n.id === connection.target)
      if (!sourceNode || !targetNode) return
      await connectEdge(
        sourceNode.uri,
        targetNode.uri,
        connection.targetHandle,
      )
    },
    [],
  )

  const onNodesChange = useCallback(
    (changes: NodeChange[]) => {
      for (const ch of changes) {
        if (ch.type === 'position' && ch.dragging === false && ch.position) {
          moveNode(ch.id, ch.position)
        }
      }
    },
    [moveNode],
  )

  return (
    <div style={{ width: '100%', height: '100%' }}>
      <ReactFlow
        nodes={nodes}
        edges={edges}
        onNodesChange={onNodesChange}
        onConnect={onConnect}
        nodeTypes={nodeTypes}
        fitView
      >
        <Background />
        <Controls />
      </ReactFlow>
    </div>
  )
}
