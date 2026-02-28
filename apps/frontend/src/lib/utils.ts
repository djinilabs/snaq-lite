/**
 * Generic helpers (e.g. UUID for widgetId).
 */

export function generateWidgetId(): string {
  return `w-${Math.random().toString(36).slice(2, 11)}`
}
