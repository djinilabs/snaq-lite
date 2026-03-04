/**
 * Unit tests for blob URL cache (register / get / unregister).
 */

import { describe, it, expect, beforeEach } from 'vitest'
import {
  registerBlobUrl,
  getBlobForUrl,
  unregisterBlobUrl,
} from './blob-url-cache'

describe('blob-url-cache', () => {
  const blobUrl = 'blob:http://localhost:3000/uuid-123'
  const blob = new Blob(['1\n2\n3'], { type: 'text/plain' })

  beforeEach(() => {
    unregisterBlobUrl(blobUrl)
  })

  it('getBlobForUrl returns undefined when not registered', () => {
    expect(getBlobForUrl(blobUrl)).toBeUndefined()
  })

  it('getBlobForUrl returns blob after registerBlobUrl', () => {
    registerBlobUrl(blobUrl, blob)
    expect(getBlobForUrl(blobUrl)).toBe(blob)
  })

  it('getBlobForUrl returns undefined after unregisterBlobUrl', () => {
    registerBlobUrl(blobUrl, blob)
    unregisterBlobUrl(blobUrl)
    expect(getBlobForUrl(blobUrl)).toBeUndefined()
  })

  it('registerBlobUrl only stores blob: URLs', () => {
    registerBlobUrl('https://example.com/file', blob)
    expect(getBlobForUrl('https://example.com/file')).toBeUndefined()
  })
})
