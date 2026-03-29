import { describe, expect, it, vi } from 'vitest'
import { fetchFirstPage, fetchNextPage } from './pagination'
import type { LspClient } from './client'

function makeClient(fetchResultSlice: LspClient['fetchResultSlice']): LspClient {
  return {
    initialize: vi.fn(async () => undefined),
    onNotification: vi.fn(),
    sendRequest: vi.fn(),
    sendNotification: vi.fn(),
    bootstrapSession: vi.fn(),
    applyPatch: vi.fn(),
    fetchResultSlice,
    close: vi.fn(),
  }
}

describe('pagination helpers', () => {
  it('fetches first page with zero offset', async () => {
    const fetchResultSlice = vi.fn(async () => ({
      elements: [1, 2],
      totalCount: 4,
      hasMore: true,
      nextCursor: 'c1',
    }))
    const client = makeClient(fetchResultSlice)
    const page = await fetchFirstPage(client, { resultHandle: 'h1', limit: 2 })

    expect(fetchResultSlice).toHaveBeenCalledWith({
      resultHandle: 'h1',
      path: [],
      offset: 0,
      limit: 2,
    })
    expect(page.cursor).toEqual({ cursor: 'c1', offset: 2 })
  })

  it('fetches next page using cursor continuation', async () => {
    const fetchResultSlice = vi.fn(async () => ({
      elements: [3, 4],
      totalCount: 4,
      hasMore: false,
      nextCursor: undefined,
    }))
    const client = makeClient(fetchResultSlice)
    const page = await fetchNextPage(client, {
      resultHandle: 'h1',
      limit: 2,
      cursor: { cursor: 'c1', offset: 2 },
    })

    expect(fetchResultSlice).toHaveBeenCalledWith({
      resultHandle: 'h1',
      path: [],
      offset: 2,
      limit: 2,
      cursor: 'c1',
    })
    expect(page.cursor).toEqual({ cursor: undefined, offset: 4 })
  })

})
