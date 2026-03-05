/**
 * Unit tests for fetchResultSlice: delegates to LSP client with correct method and params.
 */

import { describe, it, expect, beforeEach, vi } from 'vitest'
import { fetchResultSlice } from './fetch-result-slice'
import { LSP_METHOD_FETCH_RESULT_SLICE } from '~/lib/constants'

const mockSendRequest = vi.fn()
vi.mock('./language-client-singleton', () => ({
  getLanguageClient: () => ({
    sendRequest: mockSendRequest,
  }),
}))

describe('fetchResultSlice', () => {
  beforeEach(() => {
    mockSendRequest.mockReset()
  })

  it('calls sendRequest with fetchResultSlice method and params', async () => {
    mockSendRequest.mockResolvedValue({
      elements: [{ display: '42' }],
      totalCount: 1,
      hasMore: false,
    })
    await fetchResultSlice({
      widgetId: 'w1',
      path: [],
      offset: 0,
      limit: 50,
    })
    expect(mockSendRequest).toHaveBeenCalledTimes(1)
    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_FETCH_RESULT_SLICE,
      { widgetId: 'w1', path: [], offset: 0, limit: 50 },
    )
  })

  it('calls sendRequest with path and offset/limit for nested slice', async () => {
    mockSendRequest.mockResolvedValue({
      elements: [{ display: 'nested' }],
      totalCount: 1,
      hasMore: false,
    })
    await fetchResultSlice({
      widgetId: 'w2',
      path: [0, 'items'],
      offset: 10,
      limit: 20,
    })
    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_FETCH_RESULT_SLICE,
      { widgetId: 'w2', path: [0, 'items'], offset: 10, limit: 20 },
    )
  })

  it('returns the response from sendRequest', async () => {
    const response = {
      elements: [{ display: 'a' }, { display: 'b' }],
      totalCount: 2,
      hasMore: false,
    }
    mockSendRequest.mockResolvedValue(response)
    const result = await fetchResultSlice({
      widgetId: 'w3',
      path: [],
      offset: 0,
      limit: 10,
    })
    expect(result).toEqual(response)
  })

  it('propagates errors from sendRequest', async () => {
    mockSendRequest.mockRejectedValue(new Error('Widget not found'))
    await expect(
      fetchResultSlice({ widgetId: 'bad', path: [], offset: 0, limit: 10 }),
    ).rejects.toThrow('Widget not found')
  })
})
