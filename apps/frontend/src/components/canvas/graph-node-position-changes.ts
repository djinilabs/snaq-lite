import type { Dispatch, SetStateAction } from 'react'
import type { NodeChange } from '@xyflow/react'

/** Applied in onNodesChange: during drag update livePositions only; on drop call moveNode and clear live position. */
export function applyNodePositionChanges(
  changes: NodeChange[],
  moveNode: (id: string, position: { x: number; y: number }) => void,
  setLivePositions: Dispatch<
    SetStateAction<Record<string, { x: number; y: number }>>
  >,
): void {
  for (const ch of changes) {
    if (ch.type !== 'position' || !ch.position) continue
    if (ch.dragging === true) {
      setLivePositions((prev) => ({ ...prev, [ch.id]: ch.position! }))
    } else if (ch.dragging === false) {
      moveNode(ch.id, ch.position)
      setLivePositions((prev) => {
        const next = { ...prev }
        delete next[ch.id]
        return next
      })
    }
  }
}
