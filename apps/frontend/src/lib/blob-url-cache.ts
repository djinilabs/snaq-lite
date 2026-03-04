/**
 * Cache from blob URL to Blob so we can read file content without fetch(blobUrl).
 * fetch(blobUrl) can fail with net::ERR_FILE_NOT_FOUND in some environments (e.g. dev server).
 * When we create a blob URL on file drop we register the Blob here; when feeding streams we read via blob.text().
 *
 * Stored on globalThis so the cache survives Vite HMR: otherwise a module re-run would create a new empty Map
 * and the blob registered at drop time would be lost, causing feedUrlToStream to fall back to fetch and fail.
 */

const BLOB_CACHE_KEY = '__SNAQ_BLOB_URL_CACHE__'

function getBlobCache(): Map<string, Blob> {
  const g = typeof globalThis !== 'undefined' ? globalThis : (typeof window !== 'undefined' ? window : {})
  const existing = (g as unknown as Record<string, Map<string, Blob>>)[BLOB_CACHE_KEY]
  if (existing) return existing
  const map = new Map<string, Blob>()
  ;(g as unknown as Record<string, Map<string, Blob>>)[BLOB_CACHE_KEY] = map
  return map
}

export function registerBlobUrl(url: string, blob: Blob): void {
  if (url.startsWith('blob:')) {
    getBlobCache().set(url, blob)
  }
}

export function getBlobForUrl(url: string): Blob | undefined {
  return getBlobCache().get(url)
}

export function unregisterBlobUrl(url: string): void {
  getBlobCache().delete(url)
}
