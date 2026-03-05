/**
 * Dumb display: consumes streamed elements / display strings. Can be extended with Recharts/Chart.js.
 * Uses TEXT_WRAP_STYLE so long content (errors, display, counts) wraps and does not expand the block.
 *
 * When the backend sends "Vector (0 elements)" for a stream-backed result (e.g. CSV), it hasn't
 * materialized the stream yet. We trigger a one-time fetchResultSlice so the backend materializes,
 * caches, and sends a follow-up widget update with the real count—then the summary updates without
 * the user having to open "View details".
 */

import { useCallback, useEffect, useRef } from 'react'
import type { CSSProperties } from 'react'
import type { WidgetState } from '~/store'
import { useUIStore } from '~/store'
import { fetchResultSlice } from '~/lsp/fetch-result-slice'

/** Applied so long text wraps inside constrained result areas and does not expand the node. */
const TEXT_WRAP_STYLE: CSSProperties = {
  wordBreak: 'break-word',
  overflowWrap: 'break-word',
}

/** Stronger break for long unbroken strings (e.g. parse error token lists) so they wrap and never expand the block. */
const ERROR_WRAP_STYLE: CSSProperties = {
  wordBreak: 'break-all',
  overflowWrap: 'anywhere',
}

function copyToClipboardAndToast(text: string): void {
  void navigator.clipboard.writeText(text).then(
    () => useUIStore.getState().addToast('Copied', 'success'),
    () => useUIStore.getState().addToast('Copy failed', 'error'),
  )
}

/** Error message with wrap styles, hover tooltip (full text), and Copy button to view/copy full string. */
function ErrorWithCopy({ message }: { message: string }) {
  const onCopy = useCallback(() => copyToClipboardAndToast(message), [message])
  return (
    <div
      role="alert"
      title={message}
      style={{
        display: 'flex',
        flexWrap: 'wrap',
        alignItems: 'flex-start',
        gap: 4,
        width: '100%',
        minWidth: 0,
        maxWidth: '100%',
        overflow: 'hidden',
        boxSizing: 'border-box',
        color: 'var(--danger)',
        ...ERROR_WRAP_STYLE,
      }}
    >
      <span style={{ minWidth: 0, maxWidth: '100%', ...ERROR_WRAP_STYLE }}>{message}</span>
      <button
        type="button"
        onClick={onCopy}
        title="Copy full message"
        style={{
          flexShrink: 0,
          padding: '0 4px',
          fontSize: 11,
          border: '1px solid var(--border)',
          borderRadius: 'var(--radius-sm)',
          background: 'var(--bg-primary)',
          color: 'var(--text-muted)',
          cursor: 'pointer',
        }}
      >
        Copy
      </button>
    </div>
  )
}

interface WidgetDataViewProps {
  state: WidgetState | undefined
  /** When set, vector/map results show a "View details" control that opens the result detail modal. */
  widgetId?: string
  onViewDetails?: (widgetId: string) => void
}

/** Widget IDs we've already triggered a materialize fetch for (stream-backed "Vector (0 elements)"). */
const materializeTriggeredFor = new Set<string>()

export function WidgetDataView({ state, widgetId, onViewDetails }: WidgetDataViewProps) {
  // When we show "Vector (0 elements)" for a stream-backed result, one-time fetch to trigger backend materialization so the real count is sent and the summary updates.
  useEffect(() => {
    if (
      !widgetId ||
      state?.status !== 'Completed' ||
      state?.payload?.resultType?.toLowerCase() !== 'vector' ||
      state?.payload?.totalElements !== 0 ||
      materializeTriggeredFor.has(widgetId)
    ) {
      return
    }
    materializeTriggeredFor.add(widgetId)
    void fetchResultSlice({
      widgetId,
      path: [],
      offset: 0,
      limit: 1,
    }).catch(() => {
      materializeTriggeredFor.delete(widgetId)
    })
  }, [widgetId, state?.status, state?.payload?.resultType, state?.payload?.totalElements])

  if (!state) {
    return (
      <span
        style={{ color: 'var(--text-muted)' }}
        title="Waiting for result. Type an expression above; the result appears here after the language server runs it."
      >
        —
      </span>
    )
  }
  const { status, payload } = state
  if (status === 'Running' && payload?.elements?.length) {
    return (
      <div
        style={{
          fontSize: 13,
          fontFamily: 'var(--font-mono)',
          minWidth: 0,
          ...TEXT_WRAP_STYLE,
        }}
      >
        {payload.elements.map((el, i) =>
          el === null ? (
            <span key={i}>?</span>
          ) : 'display' in el ? (
            <span key={i}>{el.display} </span>
          ) : (
            <ErrorWithCopy key={i} message={el.message} />
          ),
        )}
      </div>
    )
  }
  if (status === 'Completed' && payload) {
    const resultType = payload.resultType
    const totalElements = payload.totalElements
    const resultSummary = payload.resultSummary
    const display = payload.display
    const rt = resultType?.toLowerCase()

    const canOpenDetails =
      widgetId != null &&
      onViewDetails != null &&
      (rt === 'vector' || rt === 'map' || (totalElements != null && totalElements > 1))

    if (rt === 'vector' || (totalElements != null && totalElements > 1 && rt !== 'map' && rt !== 'scalar')) {
      const n = resultSummary?.length ?? totalElements ?? 0
      return (
        <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexWrap: 'wrap', minWidth: 0 }}>
          <span style={TEXT_WRAP_STYLE}>Vector ({n} elements)</span>
          {canOpenDetails && (
            <button
              type="button"
              data-testid="view-details-btn"
              onClick={() => onViewDetails(widgetId)}
              style={{
                padding: '2px 8px',
                fontSize: 11,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-secondary)',
                color: 'var(--text)',
                cursor: 'pointer',
              }}
            >
              View details
            </button>
          )}
        </div>
      )
    }
    if (rt === 'map') {
      const keyCount = resultSummary?.keyCount ?? resultSummary?.keys?.length ?? totalElements ?? 0
      return (
        <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexWrap: 'wrap', minWidth: 0 }}>
          <span style={TEXT_WRAP_STYLE}>Map ({keyCount} keys)</span>
          {canOpenDetails && (
            <button
              type="button"
              data-testid="view-details-btn"
              onClick={() => onViewDetails(widgetId)}
              style={{
                padding: '2px 8px',
                fontSize: 11,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-secondary)',
                color: 'var(--text)',
                cursor: 'pointer',
              }}
            >
              View details
            </button>
          )}
        </div>
      )
    }
    if (rt === 'undefined') {
      return (
        <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexWrap: 'wrap', minWidth: 0 }}>
          <span style={{ fontFamily: 'var(--font-mono)', ...TEXT_WRAP_STYLE }}>
            {display ?? 'undefined'}
          </span>
        </div>
      )
    }
    if (display != null) {
      return (
        <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexWrap: 'wrap', minWidth: 0 }}>
          <span style={{ fontFamily: 'var(--font-mono)', ...TEXT_WRAP_STYLE }}>{display}</span>
          {widgetId != null && onViewDetails != null && (
            <button
              type="button"
              data-testid="view-details-btn"
              onClick={() => onViewDetails(widgetId)}
              style={{
                padding: '2px 8px',
                fontSize: 11,
                border: '1px solid var(--border)',
                borderRadius: 'var(--radius-sm)',
                background: 'var(--bg-secondary)',
                color: 'var(--text)',
                cursor: 'pointer',
              }}
            >
              View details
            </button>
          )}
        </div>
      )
    }
  }
  if (
    status === 'Completed' &&
    payload?.totalElements != null &&
    (payload?.resultType == null || payload?.resultType === '')
  ) {
    return (
      <div style={{ display: 'flex', alignItems: 'center', gap: 8, flexWrap: 'wrap', minWidth: 0 }}>
        <span style={TEXT_WRAP_STYLE}>Vector ({payload.totalElements} elements)</span>
        {widgetId != null && onViewDetails != null && (
          <button
            type="button"
            data-testid="view-details-btn"
            onClick={() => onViewDetails(widgetId)}
            style={{
              padding: '2px 8px',
              fontSize: 11,
              border: '1px solid var(--border)',
              borderRadius: 'var(--radius-sm)',
              background: 'var(--bg-secondary)',
              color: 'var(--text)',
              cursor: 'pointer',
            }}
          >
            View details
          </button>
        )}
      </div>
    )
  }
  if (status === 'Error' && payload?.message) {
    return <ErrorWithCopy message={payload.message} />
  }
  if (status === 'Cancelled') {
    return <span style={{ color: 'var(--text-muted)' }}>Cancelled</span>
  }
  return <span style={{ color: 'var(--text-muted)', ...TEXT_WRAP_STYLE }}>{status}</span>
}
