import { describe, it, expect, beforeEach } from 'vitest'
import {
  setLanguageClient,
  getLanguageClient,
  hasLanguageClient,
  whenClientReady,
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

  it('whenClientReady runs callback immediately when client already set', () => {
    const client = { sendRequest: () => Promise.resolve(), sendNotification: () => {} }
    setLanguageClient(client)
    let ran = false
    whenClientReady(() => {
      ran = true
    })
    expect(ran).toBe(true)
  })

  it('whenClientReady runs callback when setLanguageClient is called later', () => {
    let ran = false
    whenClientReady(() => {
      ran = true
    })
    expect(ran).toBe(false)
    setLanguageClient({ sendRequest: () => Promise.resolve(), sendNotification: () => {} })
    expect(ran).toBe(true)
  })
})
