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
}

export const useWidgetStore = create<WidgetStoreState>((set) => ({
  byId: {},
  setWidget: (widgetId, state) =>
    set((s) => ({ byId: { ...s.byId, [widgetId]: state } })),
  removeWidget: (widgetId) =>
    set((s) => {
      const next = { ...s.byId }
      delete next[widgetId]
      return { byId: next }
    }),
}))
