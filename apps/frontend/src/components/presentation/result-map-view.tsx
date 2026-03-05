/**
 * Virtualized table for map result slice. Fetches pages via fetchResultSlice and renders key/value rows.
 */

import { useCallback, useEffect, useRef, useState } from 'react'
import { useVirtualizer } from '@tanstack/react-virtual'
import { fetchResultSlice } from '~/lsp/fetch-result-slice'
import { RESULT_SLICE_PAGE_SIZE } from '~/lib/constants'
import type { PathSegment, ResultSliceElement } from '~/lsp/types'

const ROW_HEIGHT = 36
const EVICTION_PAGE_THRESHOLD = 3

interface MapRow {
  key: string
  value: ResultSliceElement
}

function isDisplayElement(el: ResultSliceElement): el is { display: string } {
  return el != null && typeof el === 'object' && 'display' in el && typeof (el as { display: string }).display === 'string'
}

function isVectorElement(el: ResultSliceElement): el is { type: 'vector'; path: PathSegment[] } {
  return el != null && typeof el === 'object' && (el as { type?: string }).type === 'vector'
}

function isMapElement(el: ResultSliceElement): el is { type: 'map'; path: PathSegment[] } {
  return el != null && typeof el === 'object' && (el as { type?: string }).type === 'map'
}

function valueToDisplay(el: ResultSliceElement): string {
  if (el == null) return '—'
  if (isDisplayElement(el)) return el.display
  if (isVectorElement(el)) return '<vector>'
  if (isMapElement(el)) return '<map>'
  if (typeof el === 'object' && 'key' in el && 'value' in el) return valueToDisplay((el as { value: ResultSliceElement }).value)
  return '—'
}

interface ResultMapViewProps {
  widgetId: string
  path?: PathSegment[]
  initialTotalCount?: number
  onOpenNested?: (path: PathSegment[], type: 'vector' | 'map') => void
}

export function ResultMapView({
  widgetId,
  path = [],
  initialTotalCount,
  onOpenNested,
}: ResultMapViewProps) {
  const [rows, setRows] = useState<MapRow[]>([])
  const [startOffset, setStartOffset] = useState(0)
  const [totalCount, setTotalCount] = useState(initialTotalCount ?? 0)
  const [loading, setLoading] = useState(true)
  const [error, setError] = useState<string | null>(null)
  const [hasMore, setHasMore] = useState(true)
  const parentRef = useRef<HTMLDivElement>(null)
  const loadingMoreRef = useRef(false)
  const loadingStartRef = useRef(false)

  type LoadMode = 'replace' | 'append' | 'prepend'
  const loadPage = useCallback(
    async (offset: number, mode: LoadMode = 'replace') => {
      if (mode === 'prepend') {
        if (loadingStartRef.current) return
        loadingStartRef.current = true
      } else {
        if (loadingMoreRef.current) return
        loadingMoreRef.current = true
      }
      if (offset === 0 || mode === 'replace') setLoading(true)
      setError(null)
      try {
        const res = await fetchResultSlice({
          widgetId,
          path,
          offset,
          limit: RESULT_SLICE_PAGE_SIZE,
        })
        setTotalCount(res.totalCount)
        setHasMore(res.hasMore)
        const newRows: MapRow[] = res.elements
          .filter((el): el is { key: string; value: ResultSliceElement } =>
            el != null && typeof el === 'object' && 'key' in el && 'value' in el
          )
          .map((el) => ({ key: el.key, value: el.value }))
        if (mode === 'replace' || offset === 0) {
          setRows(newRows)
          setStartOffset(0)
        } else if (mode === 'append') {
          setRows((prev) => [...prev, ...newRows])
        } else {
          setRows((prev) => [...newRows, ...prev])
          setStartOffset(offset)
        }
      } catch (e) {
        const message = e instanceof Error ? e.message : String(e)
        setError(message)
        if (offset === 0) setRows([])
      } finally {
        setLoading(false)
        if (mode === 'prepend') loadingStartRef.current = false
        else loadingMoreRef.current = false
      }
    },
    [widgetId, path],
  )

  useEffect(() => {
    void loadPage(0, 'replace')
  }, [loadPage])

  const virtualizer = useVirtualizer({
    count: totalCount || 0,
    getScrollElement: () => parentRef.current,
    estimateSize: () => ROW_HEIGHT,
    overscan: 10,
  })

  const virtualItems = virtualizer.getVirtualItems()
  const firstVisibleIndex = virtualItems[0]?.index ?? -1
  const lastVisibleIndex = virtualItems[virtualItems.length - 1]?.index ?? -1
  const windowEnd = startOffset + rows.length

  useEffect(() => {
    if (!hasMore || loading || error) return
    const needMore = lastVisibleIndex >= windowEnd - 5 && windowEnd < totalCount
    if (needMore) {
      void loadPage(windowEnd, 'append')
    }
  }, [hasMore, loading, error, windowEnd, totalCount, lastVisibleIndex, loadPage])

  useEffect(() => {
    if (firstVisibleIndex < 0 || startOffset === 0 || loading || error) return
    if (firstVisibleIndex < startOffset) {
      const fetchOffset = Math.max(0, startOffset - RESULT_SLICE_PAGE_SIZE)
      void loadPage(fetchOffset, 'prepend')
    }
  }, [firstVisibleIndex, startOffset, loading, error, loadPage])

  useEffect(() => {
    if (
      rows.length <= EVICTION_PAGE_THRESHOLD * RESULT_SLICE_PAGE_SIZE ||
      lastVisibleIndex <= startOffset + RESULT_SLICE_PAGE_SIZE
    ) {
      return
    }
    setStartOffset((s) => s + RESULT_SLICE_PAGE_SIZE)
    setRows((prev) => prev.slice(RESULT_SLICE_PAGE_SIZE))
  }, [rows.length, lastVisibleIndex, startOffset])

  if (error) {
    return (
      <div
        data-testid="result-map-view-error"
        style={{ padding: 16, color: 'var(--danger)' }}
      >
        {error}
      </div>
    )
  }

  if (loading && rows.length === 0) {
    return (
      <div style={{ padding: 16, color: 'var(--text-muted)' }}>
        Loading…
      </div>
    )
  }

  return (
    <div
      data-testid="result-map-view"
      ref={parentRef}
      style={{
        height: '100%',
        minHeight: 200,
        overflow: 'auto',
      }}
    >
      <div
        style={{
          display: 'grid',
          gridTemplateColumns: '30% 1fr',
          fontFamily: 'var(--font-mono)',
          fontSize: 12,
          borderBottom: '1px solid var(--border)',
          position: 'sticky',
          top: 0,
          background: 'var(--bg-secondary)',
          zIndex: 1,
        }}
      >
        <div style={{ padding: '8px 12px', fontWeight: 600 }}>Key</div>
        <div style={{ padding: '8px 12px', fontWeight: 600 }}>Value</div>
      </div>
      <div
        style={{
          height: `${virtualizer.getTotalSize()}px`,
          position: 'relative',
          width: '100%',
        }}
      >
        {virtualizer.getVirtualItems().map((virtualRow) => {
          const index = virtualRow.index
          const row =
            index >= startOffset && index < windowEnd
              ? rows[index - startOffset]
              : undefined
          return (
            <div
              key={virtualRow.key}
              data-index={virtualRow.index}
              style={{
                position: 'absolute',
                top: 0,
                left: 0,
                width: '100%',
                height: `${virtualRow.size}px`,
                transform: `translateY(${virtualRow.start}px)`,
                display: 'grid',
                gridTemplateColumns: '30% 1fr',
                borderBottom: '1px solid var(--border)',
                alignItems: 'center',
              }}
            >
              <div style={{ padding: '4px 12px', wordBreak: 'break-word' }}>
                {row?.key ?? '—'}
              </div>
              <div style={{ padding: '4px 12px', wordBreak: 'break-word' }}>
                {row && isVectorElement(row.value) && onOpenNested ? (
                  <button
                    type="button"
                    onClick={() => onOpenNested(row.value.path, 'vector')}
                    style={{
                      background: 'none',
                      border: 'none',
                      padding: 0,
                      color: 'var(--link)',
                      cursor: 'pointer',
                      font: 'inherit',
                    }}
                  >
                    Vector →
                  </button>
                ) : row && isMapElement(row.value) && onOpenNested ? (
                  <button
                    type="button"
                    onClick={() => onOpenNested(row.value.path, 'map')}
                    style={{
                      background: 'none',
                      border: 'none',
                      padding: 0,
                      color: 'var(--link)',
                      cursor: 'pointer',
                      font: 'inherit',
                    }}
                  >
                    Map →
                  </button>
                ) : (
                  row ? valueToDisplay(row.value) : '—'
                )}
              </div>
            </div>
          )
        })}
      </div>
      {loading && rows.length > 0 && (
        <div style={{ padding: 8, textAlign: 'center', color: 'var(--text-muted)', fontSize: 12 }}>
          Loading more…
        </div>
      )}
    </div>
  )
}
