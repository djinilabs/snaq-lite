/**
 * Pure helper for drag handle selector. Used by graph-canvas and tests.
 */

import { getNodeDragHandleClassName, type NodeKind } from './node-interaction-shell'

export function getDragHandleSelector(type: NodeKind): string {
  return `.${getNodeDragHandleClassName(type)}`
}
