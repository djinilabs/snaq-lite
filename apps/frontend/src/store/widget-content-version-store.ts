/**
 * Content version per widget ID. Incremented when editor content changes so
 * WidgetSubscription can re-subscribe. Stored in a separate store so the
 * computation node does not re-render when the user types (preserves editor focus).
 */

import { create } from 'zustand'

interface WidgetContentVersionState {
  byWidgetId: Record<string, number>
  increment: (widgetId: string) => void
}

export const useWidgetContentVersionStore = create<WidgetContentVersionState>((set) => ({
  byWidgetId: {},
  increment: (widgetId) =>
    set((s) => ({
      byWidgetId: {
        ...s.byWidgetId,
        [widgetId]: (s.byWidgetId[widgetId] ?? 0) + 1,
      },
    })),
}))
