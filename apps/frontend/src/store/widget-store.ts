/**
 * Per-widget state from snaqlite/graph/widgetDataUpdate. Updated by message router.
 */

import { create } from 'zustand'
import type { WidgetDataStatus } from '~/lsp/types'

export interface WidgetState {
  status: WidgetDataStatus
  payload?: {
    elements?: Array<{ display: string } | null | { kind: 'error'; message: string }>
    offset?: number
    count?: number
    display?: string
    totalElements?: number
    message?: string
    reason?: string
  }
}

interface WidgetStoreState {
  byId: Record<string, WidgetState>
  setWidget: (widgetId: string, state: WidgetState) => void
  removeWidget: (widgetId: string) => void
  clearAll: () => void
}

/**
 * Merges incoming state with current: appends elements when both are Running with elements;
 * otherwise returns incoming (replaces on Completed/Cancelled/Error or first Running).
 */
function mergeWidgetState(
  current: WidgetState | undefined,
  incoming: WidgetState,
): WidgetState {
  if (incoming.status !== 'Running' || incoming.payload?.elements == null) {
    return incoming
  }
  if (
    current?.status === 'Running' &&
    current.payload?.elements != null
  ) {
    const accumulated = [...current.payload.elements, ...incoming.payload.elements]
    return {
      status: 'Running',
      payload: {
        ...incoming.payload,
        elements: accumulated,
        offset: incoming.payload.offset,
        count: accumulated.length,
      },
    }
  }
  return incoming
}

export const useWidgetStore = create<WidgetStoreState>((set) => ({
  byId: {},
  setWidget: (widgetId, state) =>
    set((s) => {
      const current = s.byId[widgetId]
      const merged = mergeWidgetState(current, state)
      return { byId: { ...s.byId, [widgetId]: merged } }
    }),
  removeWidget: (widgetId) =>
    set((s) => {
      const next = { ...s.byId }
      delete next[widgetId]
      return { byId: next }
    }),
  clearAll: () => set({ byId: {} }),
}))
