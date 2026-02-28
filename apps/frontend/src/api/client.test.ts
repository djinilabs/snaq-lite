import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import { getBaseUrl, apiFetch } from './client'

describe('api/client', () => {
  describe('getBaseUrl', () => {
    it('returns a string', () => {
      expect(typeof getBaseUrl()).toBe('string')
    })
  })

  describe('apiFetch', () => {
    beforeEach(() => {
      vi.stubGlobal('fetch', vi.fn())
    })
    afterEach(() => {
      vi.unstubAllGlobals()
    })

    it('calls fetch and returns a Promise', async () => {
      const fetchMock = vi.mocked(fetch).mockResolvedValue(new Response())
      const res = apiFetch('foo')
      expect(res).toBeInstanceOf(Promise)
      await res
      expect(fetchMock).toHaveBeenCalled()
      const [url] = fetchMock.mock.calls[0]
      expect(url).toContain('foo')
    })

    it('passes init to fetch', async () => {
      const fetchMock = vi.mocked(fetch).mockResolvedValue(new Response())
      await apiFetch('bar', { method: 'POST', body: '{}' })
      expect(fetchMock).toHaveBeenCalledWith(expect.any(String), { method: 'POST', body: '{}' })
    })
  })
})
