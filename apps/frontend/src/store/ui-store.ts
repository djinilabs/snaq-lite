/**
 * Optional UI state: toasts, error state, sidebar visibility, etc.
 */

import { create } from 'zustand'

export interface Toast {
  id: string
  message: string
  kind?: 'info' | 'error' | 'success'
}

interface UIState {
  toasts: Toast[]
  addToast: (message: string, kind?: Toast['kind']) => void
  removeToast: (id: string) => void
  /** When set, the result detail modal is open for this widget (single modal at a time). */
  resultDetailWidgetId: string | null
  setResultDetailWidgetId: (widgetId: string | null) => void
}

export const useUIStore = create<UIState>((set) => ({
  toasts: [],
  resultDetailWidgetId: null,
  setResultDetailWidgetId: (widgetId) => set({ resultDetailWidgetId: widgetId }),

  addToast: (message, kind = 'info') =>
    set((state) => ({
      toasts: state.toasts.concat({
        id: Math.random().toString(36).slice(2),
        message,
        kind,
      }),
    })),

  removeToast: (id) =>
    set((state) => ({
      toasts: state.toasts.filter((t) => t.id !== id),
    })),
}))
