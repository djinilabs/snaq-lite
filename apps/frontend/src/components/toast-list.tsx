/**
 * Renders toasts from the UI store (errors, info, success).
 */

import { useUIStore } from '~/store'

export function ToastList() {
  const toasts = useUIStore((s) => s.toasts)
  const removeToast = useUIStore((s) => s.removeToast)

  if (toasts.length === 0) return null

  return (
    <div
      style={{
        position: 'fixed',
        bottom: 24,
        right: 24,
        zIndex: 9999,
        display: 'flex',
        flexDirection: 'column',
        gap: 8,
        maxWidth: 400,
      }}
    >
      {toasts.map((t) => (
        <div
          key={t.id}
          role="alert"
          style={{
            padding: '12px 16px',
            borderRadius: 'var(--radius-sm)',
            background: t.kind === 'error' ? 'var(--danger-soft)' : 'var(--bg-elevated)',
            color: t.kind === 'error' ? 'var(--danger)' : 'var(--text-primary)',
            border: '1px solid var(--border)',
            boxShadow: 'var(--shadow)',
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'space-between',
            gap: 12,
          }}
        >
          <span style={{ flex: 1, fontSize: 14 }}>{t.message}</span>
          <button
            type="button"
            aria-label="Dismiss"
            onClick={() => removeToast(t.id)}
            style={{
              padding: 4,
              background: 'transparent',
              border: 'none',
              color: 'var(--text-muted)',
              cursor: 'pointer',
              fontSize: 18,
              lineHeight: 1,
            }}
          >
            ×
          </button>
        </div>
      ))}
    </div>
  )
}
