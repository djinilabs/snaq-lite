import type { FetchResultSliceResponse } from './types'
import type { LspClient } from './client'

export type PageCursor = {
  cursor?: string
  offset: number
}

export async function fetchFirstPage(
  client: LspClient,
  params: { resultHandle: string; limit: number; path?: Array<number | string> },
): Promise<{ response: FetchResultSliceResponse; cursor: PageCursor }> {
  const response = await client.fetchResultSlice({
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
  const response = await client.fetchResultSlice({
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
