import type { FetchResultSliceResponse } from './types'
import type { LspClient } from './client'

const LSP_FETCH_RESULT_SLICE_TIMEOUT_MS = 10_000

export type PageCursor = {
  cursor?: string
  offset: number
}

async function fetchResultSliceWithTimeout(
  client: LspClient,
  params: Parameters<LspClient['fetchResultSlice']>[0],
): Promise<FetchResultSliceResponse> {
  return await new Promise<FetchResultSliceResponse>((resolve, reject) => {
    let settled = false
    const timeoutId = setTimeout(() => {
      if (settled) {
        return
      }
      settled = true
      reject(new Error(`fetchResultSlice timed out after ${LSP_FETCH_RESULT_SLICE_TIMEOUT_MS}ms`))
    }, LSP_FETCH_RESULT_SLICE_TIMEOUT_MS)
    client.fetchResultSlice(params).then(
      (response) => {
        if (settled) {
          return
        }
        settled = true
        clearTimeout(timeoutId)
        resolve(response)
      },
      (error) => {
        if (settled) {
          return
        }
        settled = true
        clearTimeout(timeoutId)
        reject(error)
      },
    )
  })
}

export async function fetchFirstPage(
  client: LspClient,
  params: { resultHandle: string; limit: number; path?: Array<number | string> },
): Promise<{ response: FetchResultSliceResponse; cursor: PageCursor }> {
  if (params.limit <= 0) {
    throw new Error('Page size must be greater than zero')
  }
  const response = await fetchResultSliceWithTimeout(client, {
    resultHandle: params.resultHandle,
    path: params.path ?? [],
    offset: 0,
    limit: params.limit,
  })
  return { response, cursor: { cursor: response.nextCursor, offset: response.elements.length } }
}

export async function fetchNextPage(
  client: LspClient,
  params: {
    resultHandle: string
    limit: number
    cursor: PageCursor
    path?: Array<number | string>
  },
): Promise<{ response: FetchResultSliceResponse; cursor: PageCursor }> {
  if (params.limit <= 0) {
    throw new Error('Page size must be greater than zero')
  }
  if (!params.cursor.cursor) {
    throw new Error('Cursor continuation is required for fetchNextPage')
  }
  const response = await fetchResultSliceWithTimeout(client, {
    resultHandle: params.resultHandle,
    path: params.path ?? [],
    offset: params.cursor.offset,
    limit: params.limit,
    cursor: params.cursor.cursor,
  })
  return {
    response,
    cursor: {
      cursor: response.nextCursor,
      offset: params.cursor.offset + response.elements.length,
    },
  }
}
