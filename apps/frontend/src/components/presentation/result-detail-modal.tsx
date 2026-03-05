/**
 * Modal dialog for viewing computation result details (scalar, vector list, or map table).
 * Single modal at a time; close via Escape or close button. Focus trap inside modal.
 * Supports nested navigation: click a vector/map row to drill down; Back to go up.
 */

import { useEffect, useRef, useCallback, useState } from 'react'
import { createPortal } from 'react-dom'
import { useUIStore, useWidgetStore } from '~/store'
import { ResultVectorView } from './result-vector-view'
import { ResultMapView } from './result-map-view'
import type { PathSegment } from '~/lsp/types'

const FOCUSABLE_SELECTOR =
  'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'

function getFocusableElements(container: HTMLElement): HTMLElement[] {
  return Array.from(container.querySelectorAll<HTMLElement>(FOCUSABLE_SELECTOR))
}

type PathEntry = { path: PathSegment[]; type: 'vector' | 'map' }

export function ResultDetailModal() {
  const widgetId = useUIStore((s) => s.resultDetailWidgetId)
  const setResultDetailWidgetId = useUIStore((s) => s.setResultDetailWidgetId)
  const widgetState = useWidgetStore((s) => (widgetId ? s.byId[widgetId] : undefined))
  const dialogRef = useRef<HTMLDivElement>(null)
  const [pathStack, setPathStack] = useState<PathEntry[]>([])

  useEffect(() => {
    setPathStack([])
  }, [widgetId])

  const close = useCallback(() => {
    setResultDetailWidgetId(null)
  }, [setResultDetailWidgetId])

  const current =
    pathStack.length === 0
      ? null
      : pathStack[pathStack.length - 1]
  const currentPath = current?.path ?? []
  const currentType = current?.type ?? null

  const onOpenNested = useCallback((path: PathSegment[], type: 'vector' | 'map') => {
    setPathStack((prev) => [...prev, { path, type }])
  }, [])

  const onBack = useCallback(() => {
    setPathStack((prev) => prev.slice(0, -1))
  }, [])

  useEffect(() => {
    if (!widgetId) return
    const onKeyDown = (e: KeyboardEvent) => {
      if (e.key === 'Escape') {
        e.preventDefault()
        close()
        return
      }
      const dialog = dialogRef.current
      if (!dialog || e.key !== 'Tab') return
      const focusables = getFocusableElements(dialog)
      if (focusables.length === 0) return
      const first = focusables[0]
      const last = focusables[focusables.length - 1]
      const active = document.activeElement as HTMLElement | null
      if (e.shiftKey) {
        if (active === first) {
          e.preventDefault()
          last.focus()
        }
      } else {
        if (active === last) {
          e.preventDefault()
          first.focus()
        }
      }
    }
    document.addEventListener('keydown', onKeyDown)
    return () => document.removeEventListener('keydown', onKeyDown)
  }, [widgetId, close])

  useEffect(() => {
    if (!widgetId || !dialogRef.current) return
    const focusables = getFocusableElements(dialogRef.current)
    const first = focusables[0]
    if (first) {
      first.focus()
    }
  }, [widgetId])

  if (!widgetId || typeof document === 'undefined') return null

  const status = widgetState?.status
  const payload = widgetState?.payload
  const resultType = payload?.resultType
  const rt = resultType?.toLowerCase()
  const display = payload?.display ?? (rt === 'undefined' ? 'undefined' : undefined)
  const scalarDisplay = display ?? (payload?.totalElements != null ? `${payload.totalElements} elements` : null) ?? '—'

  const hasVectorSummary = payload?.resultSummary?.length != null
  const hasMapSummary = payload?.resultSummary?.keyCount != null || (payload?.resultSummary?.keys?.length ?? 0) > 0
  const viewType =
    currentType ??
    (rt === 'vector' ? 'vector' : rt === 'map' ? 'map' : payload?.totalElements != null ? 'vector' : hasVectorSummary ? 'vector' : hasMapSummary ? 'map' : null)
  const viewPath = currentType ? currentPath : []
  const viewInitialTotal =
    pathStack.length === 0
      ? payload?.totalElements ?? payload?.resultSummary?.length ?? payload?.resultSummary?.keyCount ?? payload?.resultSummary?.keys?.length
      : undefined

  const content =
    status === 'Completed' && payload ? (
      viewType === 'vector' ? (
        <div style={{ flex: 1, minHeight: 0, display: 'flex', flexDirection: 'column' }}>
          {pathStack.length > 0 && (
            <button
              type="button"
              onClick={onBack}
              style={{
                margin: '8px 16px',
                padding: '4px 12px',
                fontSize: 12,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-secondary)',
                cursor: 'pointer',
              }}
            >
              ← Back
            </button>
          )}
          <ResultVectorView
            widgetId={widgetId}
            path={viewPath}
            initialTotalCount={viewInitialTotal}
            onOpenNested={onOpenNested}
          />
        </div>
      ) : viewType === 'map' ? (
        <div style={{ flex: 1, minHeight: 0, display: 'flex', flexDirection: 'column' }}>
          {pathStack.length > 0 && (
            <button
              type="button"
              onClick={onBack}
              style={{
                margin: '8px 16px',
                padding: '4px 12px',
                fontSize: 12,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-secondary)',
                cursor: 'pointer',
              }}
            >
              ← Back
            </button>
          )}
          <ResultMapView
            widgetId={widgetId}
            path={viewPath}
            initialTotalCount={viewInitialTotal}
            onOpenNested={onOpenNested}
          />
        </div>
      ) : rt === 'vector' || rt === 'map' ? null : (
        <div
          style={{
            padding: 16,
            fontFamily: 'var(--font-mono)',
            wordBreak: 'break-word',
          }}
        >
          {scalarDisplay}
        </div>
      )
    ) : status === 'Error' && payload?.message ? (
      <div style={{ padding: 16, color: 'var(--danger)' }}>{payload.message}</div>
    ) : status === 'Cancelled' ? (
      <div style={{ padding: 16, color: 'var(--text-muted)' }}>Result was cancelled.</div>
    ) : (
      <div style={{ padding: 16, color: 'var(--text-muted)' }}>Loading…</div>
    )

  const modal = (
    <div
      role="presentation"
      data-testid="result-detail-overlay"
      style={{
        position: 'fixed',
        inset: 0,
        zIndex: 10_000,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        background: 'rgba(0,0,0,0.4)',
      }}
      onClick={(e) => {
        if (e.target === e.currentTarget) close()
      }}
    >
      <div
        ref={dialogRef}
        role="dialog"
        aria-modal="true"
        aria-labelledby="result-detail-title"
        data-testid="result-detail-modal"
        style={{
          background: 'var(--bg-primary)',
          border: '1px solid var(--border)',
          borderRadius: 'var(--radius)',
          boxShadow: 'var(--shadow)',
          maxWidth: '90vw',
          maxHeight: '80vh',
          minWidth: 320,
          display: 'flex',
          flexDirection: 'column',
          overflow: 'hidden',
        }}
        onClick={(e) => e.stopPropagation()}
      >
        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            justifyContent: 'space-between',
            padding: '12px 16px',
            borderBottom: '1px solid var(--border)',
          }}
        >
          <h2
            id="result-detail-title"
            style={{ margin: 0, fontSize: 14, fontWeight: 600 }}
          >
            Result details
          </h2>
          <button
            type="button"
            data-testid="result-detail-close-btn"
            aria-label="Close"
            onClick={close}
            style={{
              padding: 4,
              border: 'none',
              background: 'transparent',
              color: 'var(--text-muted)',
              cursor: 'pointer',
              fontSize: 18,
              lineHeight: 1,
            }}
          >
            ×
          </button>
        </div>
        <div style={{ overflow: 'auto', flex: 1 }}>{content}</div>
      </div>
    </div>
  )

  return createPortal(modal, document.body!)
}
