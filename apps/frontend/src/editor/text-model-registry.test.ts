/**
 * Unit tests for text-model-registry: model map, onModelCreated callback, dispose.
 */

import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest'
import {
  setOnModelCreated,
  setOnModelDisposed,
  getOrCreateModel,
  getModel,
  hasModel,
  disposeModel,
  disposeAllGraphModels,
} from './text-model-registry'
import { nodeIdToUri } from './virtual-uri'

const TEST_URI = 'snaq://graph/on-created-test.sl'

describe('text-model-registry', () => {
  const fakeModel = { dispose: vi.fn(), getValue: vi.fn(() => ''), getVersionId: vi.fn(() => 1) }
  const createModel = vi.fn(() => fakeModel)
  const monaco = {
    editor: { createModel },
    Uri: { parse: (s: string) => ({ toString: () => s }) },
  } as unknown as typeof import('monaco-editor')

  beforeEach(() => {
    createModel.mockClear()
    fakeModel.dispose.mockClear()
    disposeModel(TEST_URI)
  })

  afterEach(() => {
    disposeModel(TEST_URI)
    setOnModelCreated(() => {})
    setOnModelDisposed(() => {})
  })

  describe('getOrCreateModel and onModelCreated', () => {
    it('invokes onModelCreated when a new model is created', () => {
      const onModelCreated = vi.fn()
      setOnModelCreated(onModelCreated)

      getOrCreateModel(TEST_URI, monaco, 'initial')

      expect(createModel).toHaveBeenCalledWith('initial', 'snaq', expect.anything())
      expect(onModelCreated).toHaveBeenCalledTimes(1)
      expect(onModelCreated).toHaveBeenCalledWith(TEST_URI)
    })

    it('does not invoke onModelCreated when returning an existing model', () => {
      const onModelCreated = vi.fn()
      setOnModelCreated(onModelCreated)

      getOrCreateModel(TEST_URI, monaco, 'first')
      expect(onModelCreated).toHaveBeenCalledTimes(1)

      getOrCreateModel(TEST_URI, monaco, 'second')
      expect(createModel).toHaveBeenCalledTimes(1)
      expect(onModelCreated).toHaveBeenCalledTimes(1)
    })
  })

  describe('getModel and hasModel', () => {
    it('getModel returns null when no model for URI', () => {
      expect(getModel(TEST_URI, monaco)).toBeNull()
    })

    it('getModel returns model after getOrCreateModel', () => {
      const created = getOrCreateModel(TEST_URI, monaco, '')
      expect(getModel(TEST_URI, monaco)).toBe(created)
    })

    it('hasModel returns false when no model, true after getOrCreateModel', () => {
      expect(hasModel(TEST_URI)).toBe(false)
      getOrCreateModel(TEST_URI, monaco, '')
      expect(hasModel(TEST_URI)).toBe(true)
    })
  })

  describe('disposeModel', () => {
    it('disposes model and removes from registry', () => {
      getOrCreateModel(TEST_URI, monaco, '')
      expect(hasModel(TEST_URI)).toBe(true)

      disposeModel(TEST_URI)
      expect(hasModel(TEST_URI)).toBe(false)
      expect(getModel(TEST_URI, monaco)).toBeNull()
      expect(fakeModel.dispose).toHaveBeenCalledTimes(1)
    })

    it('invokes onModelDisposed when a model is disposed', () => {
      const onModelDisposed = vi.fn()
      setOnModelDisposed(onModelDisposed)
      getOrCreateModel(TEST_URI, monaco, '')

      disposeModel(TEST_URI)

      expect(onModelDisposed).toHaveBeenCalledTimes(1)
      expect(onModelDisposed).toHaveBeenCalledWith(TEST_URI)
    })
  })

  describe('disposeAllGraphModels', () => {
    it('disposes models for given node ids via nodeIdToUri', () => {
      const uri1 = nodeIdToUri('n1')
      const uri2 = nodeIdToUri('n2')
      getOrCreateModel(uri1, monaco, '')
      getOrCreateModel(uri2, monaco, '')

      disposeAllGraphModels(['n1', 'n2'])

      expect(hasModel(uri1)).toBe(false)
      expect(hasModel(uri2)).toBe(false)
    })
  })
})
