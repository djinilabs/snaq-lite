/**
 * Shared interaction shell for canvas nodes: drag only from the title (DragZone),
 * all other content (NodeContentZone) is non-draggable so the editor and controls stay clickable.
 */

import {
  forwardRef,
  type CSSProperties,
  type ComponentPropsWithoutRef,
  type PropsWithChildren,
} from 'react'
import {
  DRAG_HANDLE_CLASS_COMPUTATION,
  DRAG_HANDLE_CLASS_FILE,
  DRAG_HANDLE_CLASS_PRESENTATION,
  NODRAG_CLASS,
  NOWHEEL_CLASS,
} from '~/lib/constants'

export type NodeKind = 'computation' | 'presentation' | 'file'

const NODE_BASE_STYLE: CSSProperties = {
  background: 'var(--bg-card)',
  border: '1px solid var(--border)',
  borderRadius: 'var(--radius)',
  minWidth: 260,
  padding: 12,
  boxShadow: 'var(--shadow)',
  cursor: 'default',
}

const DRAG_ZONE_STYLE: CSSProperties = {
  fontSize: 12,
  color: 'var(--text-muted)',
  marginBottom: 8,
  fontWeight: 500,
  cursor: 'grab',
}

export function getNodeDragHandleClassName(kind: NodeKind): string {
  switch (kind) {
    case 'computation':
      return DRAG_HANDLE_CLASS_COMPUTATION
    case 'presentation':
      return DRAG_HANDLE_CLASS_PRESENTATION
    case 'file':
      return DRAG_HANDLE_CLASS_FILE
    default:
      return DRAG_HANDLE_CLASS_COMPUTATION
  }
}

interface NodeFrameProps extends PropsWithChildren {
  kind: NodeKind
  title: string
  selected?: boolean
  minHeight?: number
  titleTestId?: string
  nodeTestId?: string
  /** Node id for E2E (data-node-id) so tests can resolve store node ids for programmatic edge add. */
  nodeId?: string
}

export function NodeFrame({
  kind,
  title,
  selected = false,
  minHeight,
  titleTestId,
  nodeTestId,
  nodeId,
  children,
}: NodeFrameProps) {
  return (
    <div
      className="nopan"
      data-testid={nodeTestId}
      {...(nodeId != null ? { 'data-node-id': nodeId } : {})}
      style={{
        ...NODE_BASE_STYLE,
        ...(typeof minHeight === 'number' ? { minHeight } : {}),
        ...(selected
          ? {
              outline: '2px solid var(--accent)',
              outlineOffset: 2,
            }
          : {}),
      }}
    >
      <div
        className={getNodeDragHandleClassName(kind)}
        data-testid={titleTestId}
        style={DRAG_ZONE_STYLE}
        title="Drag to move the block"
      >
        {title}
      </div>
      {children}
    </div>
  )
}

NodeFrame.displayName = 'NodeFrame'

interface NodeContentZoneProps
  extends PropsWithChildren,
    ComponentPropsWithoutRef<'div'> {
  nowheel?: boolean
}

export const NodeContentZone = forwardRef<HTMLDivElement, NodeContentZoneProps>(
  ({ className, nowheel = false, children, ...rest }, ref) => {
    const classes = [NODRAG_CLASS]
    if (nowheel) classes.push(NOWHEEL_CLASS)
    if (className) classes.push(className)

    return (
      <div ref={ref} className={classes.join(' ')} {...rest}>
        {children}
      </div>
    )
  },
)

NodeContentZone.displayName = 'NodeContentZone'
