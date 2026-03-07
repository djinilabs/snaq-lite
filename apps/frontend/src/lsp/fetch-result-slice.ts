/**
 * LSP request: fetch a slice of a widget result at the given path (for virtualized list/table).
 * Waits for LSP to be ready with a timeout to avoid hanging if init never completes.
 */

import { whenLspReady } from './language-client-singleton'
import {
  LSP_METHOD_FETCH_RESULT_SLICE,
  LSP_FETCH_RESULT_SLICE_TIMEOUT_MS,
} from '~/lib/constants'
import type { FetchResultSliceParams, FetchResultSliceResponse } from './types'

function whenLspReadyWithTimeout(timeoutMs: number): Promise<Awaited<ReturnType<typeof whenLspReady>>> {
  return Promise.race([
    whenLspReady(),
    new Promise<never>((_, reject) =>
      setTimeout(
        () => reject(new Error(`LSP not ready within ${timeoutMs}ms`)),
        timeoutMs,
      ),
    ),
  ])
}

export async function fetchResultSlice(
  params: FetchResultSliceParams,
): Promise<FetchResultSliceResponse> {
  const client = await whenLspReadyWithTimeout(LSP_FETCH_RESULT_SLICE_TIMEOUT_MS)
  const result = await client.sendRequest<FetchResultSliceResponse>(
    LSP_METHOD_FETCH_RESULT_SLICE,
    params,
  )
  return result
}
