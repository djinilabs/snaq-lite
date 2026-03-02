/**
 * E2E focus debugging: when window.__FOCUS_DEBUG__ is true, events are pushed to
 * window.__FOCUS_DEBUG_LOG__ so tests can correlate focus loss with React renders.
 * Set __FOCUS_DEBUG__ and clear __FOCUS_DEBUG_LOG__ in E2E before the scenario.
 */

export type FocusDebugEvent =
  | { t: number; event: 'editor-render'; nodeId: string }
  | { t: number; event: 'editor-focus-lost'; nodeId: string; activeElementTag?: string; relatedTargetTag?: string }
  | { t: number; event: 'node-render'; nodeId: string }

declare global {
  interface Window {
    __FOCUS_DEBUG__?: boolean
    __FOCUS_DEBUG_LOG__?: FocusDebugEvent[]
  }
}

function isEnabled(): boolean {
  return typeof window !== 'undefined' && window.__FOCUS_DEBUG__ === true
}

function ensureLog(): FocusDebugEvent[] {
  if (typeof window === 'undefined') return []
  if (!Array.isArray(window.__FOCUS_DEBUG_LOG__)) {
    window.__FOCUS_DEBUG_LOG__ = []
  }
  return window.__FOCUS_DEBUG_LOG__
}

export function focusDebugPush(entry: FocusDebugEvent): void {
  if (!isEnabled()) return
  ensureLog().push(entry)
}

export function focusDebugEditorRender(nodeId: string): void {
  focusDebugPush({ t: Date.now(), event: 'editor-render', nodeId })
}

export function focusDebugEditorFocusLost(
  nodeId: string,
  activeElement?: Element | null,
  relatedTarget?: EventTarget | null,
): void {
  focusDebugPush({
    t: Date.now(),
    event: 'editor-focus-lost',
    nodeId,
    activeElementTag: activeElement ? (activeElement as Element).tagName : undefined,
    relatedTargetTag: relatedTarget ? (relatedTarget as Element).tagName : undefined,
  })
}

export function focusDebugNodeRender(nodeId: string): void {
  focusDebugPush({ t: Date.now(), event: 'node-render', nodeId })
}
