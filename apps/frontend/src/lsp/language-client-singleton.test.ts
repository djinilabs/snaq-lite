import { describe, it, expect, beforeEach } from 'vitest'
import {
  setLanguageClient,
  getLanguageClient,
  hasLanguageClient,
} from './language-client-singleton'

describe('language-client-singleton', () => {
  beforeEach(() => {
    setLanguageClient(null)
  })

  it('hasLanguageClient is false when client not set', () => {
    expect(hasLanguageClient()).toBe(false)
  })

  it('getLanguageClient throws when client not set', () => {
    expect(() => getLanguageClient()).toThrow('Language client not initialized')
  })

  it('after setLanguageClient, getLanguageClient returns same object and hasLanguageClient is true', () => {
    const client = {
      sendRequest: () => Promise.resolve(),
      sendNotification: () => {},
    }
    setLanguageClient(client)
    expect(hasLanguageClient()).toBe(true)
    expect(getLanguageClient()).toBe(client)
  })

  it('after setLanguageClient(null), hasLanguageClient is false and getLanguageClient throws', () => {
    setLanguageClient({ sendRequest: () => Promise.resolve(), sendNotification: () => {} })
    setLanguageClient(null)
    expect(hasLanguageClient()).toBe(false)
    expect(() => getLanguageClient()).toThrow('Language client not initialized')
  })
})
