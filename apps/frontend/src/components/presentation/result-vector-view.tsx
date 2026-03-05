/**
 * Virtualized list for vector result slice. Fetches pages via fetchResultSlice and renders rows.
 */

import { useCallback, useEffect, useRef, useState } from 'react'
import { useVirtualizer } from '@tanstack/react-virtual'
import { fetchResultSlice } from '~/lsp/fetch-result-slice'
import { RESULT_SLICE_PAGE_SIZE } from '~/lib/constants'
import type { PathSegment, ResultSliceElement } from '~/lsp/types'

const ROW_HEIGHT = 32
/** Keep at most this many pages in memory; evict when exceeded (plan §4.5 sliding-window). */
const EVICTION_PAGE_THRESHOLD = 3

interface ResultVectorViewProps {
  widgetId: string
  path?: PathSegment[]
  initialTotalCount?: number
  onOpenNested?: (path: PathSegment[], type: 'vector' | 'map') => void
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

export function ResultVectorView({
  widgetId,
  path = [],
  initialTotalCount,
  onOpenNested,
}: ResultVectorViewProps) {
  const [items, setItems] = useState<ResultSliceElement[]>([])
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
        if (mode === 'replace' || offset === 0) {
          setItems(res.elements)
          setStartOffset(0)
        } else if (mode === 'append') {
          setItems((prev) => [...prev, ...res.elements])
        } else {
          setItems((prev) => [...res.elements, ...prev])
          setStartOffset(offset)
        }
      } catch (e) {
        const message = e instanceof Error ? e.message : String(e)
        setError(message)
        if (offset === 0) setItems([])
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
  const windowEnd = startOffset + items.length

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
      items.length <= EVICTION_PAGE_THRESHOLD * RESULT_SLICE_PAGE_SIZE ||
      lastVisibleIndex <= startOffset + RESULT_SLICE_PAGE_SIZE
    ) {
      return
    }
    setStartOffset((s) => s + RESULT_SLICE_PAGE_SIZE)
    setItems((prev) => prev.slice(RESULT_SLICE_PAGE_SIZE))
  }, [items.length, lastVisibleIndex, startOffset])

  if (error) {
    return (
      <div
        data-testid="result-vector-view-error"
        style={{ padding: 16, color: 'var(--danger)' }}
      >
        {error}
      </div>
    )
  }

  if (loading && items.length === 0) {
    return (
      <div style={{ padding: 16, color: 'var(--text-muted)' }}>
        Loading…
      </div>
    )
  }

  return (
    <div
      data-testid="result-vector-view"
      ref={parentRef}
      style={{
        height: '100%',
        minHeight: 200,
        overflow: 'auto',
      }}
    >
      <div
        style={{
          height: `${virtualizer.getTotalSize()}px`,
          width: '100%',
          position: 'relative',
        }}
      >
        {virtualizer.getVirtualItems().map((virtualRow) => {
          const index = virtualRow.index
          const el =
            index >= startOffset && index < windowEnd
              ? items[index - startOffset] ?? null
              : null
          return (
            <div
              key={virtualRow.key}
              data-index={index}
              style={{
                position: 'absolute',
                top: 0,
                left: 0,
                width: '100%',
                height: `${virtualRow.size}px`,
                transform: `translateY(${virtualRow.start}px)`,
                display: 'flex',
                alignItems: 'center',
                paddingLeft: 12,
                paddingRight: 12,
                borderBottom: '1px solid var(--border)',
                fontFamily: 'var(--font-mono)',
                fontSize: 12,
              }}
            >
              {el == null ? (
                <span style={{ color: 'var(--text-muted)' }}>—</span>
              ) : isDisplayElement(el) ? (
                <span style={{ wordBreak: 'break-word' }}>{el.display}</span>
              ) : isVectorElement(el) ? (
                onOpenNested ? (
                  <button
                    type="button"
                    onClick={() => onOpenNested(el.path, 'vector')}
                    style={{
                      background: 'none',
                      border: 'none',
                      padding: 0,
                      color: 'var(--link)',
                      cursor: 'pointer',
                      textAlign: 'left',
                      font: 'inherit',
                    }}
                  >
                    Vector →
                  </button>
                ) : (
                  <span style={{ color: 'var(--text-muted)' }}>Vector</span>
                )
              ) : isMapElement(el) ? (
                onOpenNested ? (
                  <button
                    type="button"
                    onClick={() => onOpenNested(el.path, 'map')}
                    style={{
                      background: 'none',
                      border: 'none',
                      padding: 0,
                      color: 'var(--link)',
                      cursor: 'pointer',
                      textAlign: 'left',
                      font: 'inherit',
                    }}
                  >
                    Map →
                  </button>
                ) : (
                  <span style={{ color: 'var(--text-muted)' }}>Map</span>
                )
              ) : (
                <span style={{ color: 'var(--text-muted)' }}>—</span>
              )}
            </div>
          )
        })}
      </div>
      {loading && items.length > 0 && (
        <div style={{ padding: 8, textAlign: 'center', color: 'var(--text-muted)', fontSize: 12 }}>
          Loading more…
        </div>
      )}
    </div>
  )
}
