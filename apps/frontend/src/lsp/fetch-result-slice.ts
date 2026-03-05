/**
 * LSP request: fetch a slice of a widget result at the given path (for virtualized list/table).
 */

import { getLanguageClient } from './language-client-singleton'
import { LSP_METHOD_FETCH_RESULT_SLICE } from '~/lib/constants'
import type { FetchResultSliceParams, FetchResultSliceResponse } from './types'

export async function fetchResultSlice(
  params: FetchResultSliceParams,
): Promise<FetchResultSliceResponse> {
  const client = getLanguageClient()
  const result = await client.sendRequest<FetchResultSliceResponse>(
    LSP_METHOD_FETCH_RESULT_SLICE,
    params,
  )
  return result
}
