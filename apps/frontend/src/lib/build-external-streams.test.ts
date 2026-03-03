/**
 * Unit tests for build-external-streams: parsing and buildGetExternalStreams.
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest'
import {
  parseNewlineDelimitedNumbers,
  buildGetExternalStreams,
} from './build-external-streams'

const mockRequestCreateStreamInput = vi.fn()
const mockSendStreamChunk = vi.fn()
const mockCloseStream = vi.fn()
vi.mock('~/lsp/message-router', () => ({
  requestCreateStreamInput: (...args: unknown[]) =>
    mockRequestCreateStreamInput(...args),
  sendStreamChunk: (...args: unknown[]) => mockSendStreamChunk(...args),
  closeStream: (...args: unknown[]) => mockCloseStream(...args),
}))

describe('parseNewlineDelimitedNumbers', () => {
  it('yields a single batch for a few numbers', () => {
    expect([...parseNewlineDelimitedNumbers('1\n2\n3')]).toEqual([[1, 2, 3]])
  })

  it('returns empty for empty string', () => {
    expect([...parseNewlineDelimitedNumbers('')]).toEqual([])
  })

  it('skips blank lines', () => {
    expect([...parseNewlineDelimitedNumbers('1\n\n2\n\n3')]).toEqual([[1, 2, 3]])
  })

  it('handles CRLF line endings', () => {
    expect([...parseNewlineDelimitedNumbers('1\r\n2\r\n3')]).toEqual([[1, 2, 3]])
  })

  it('skips non-finite lines', () => {
    expect([...parseNewlineDelimitedNumbers('1\nhello\n2\nNaN\n3')]).toEqual([
      [1, 2, 3],
    ])
  })

  it('trims lines before parsing', () => {
    expect([...parseNewlineDelimitedNumbers('  1  \n  2  \n  3  ')]).toEqual([
      [1, 2, 3],
    ])
  })

  it('yields multiple batches when over BATCH_SIZE', () => {
    const many = Array.from({ length: 1001 }, (_, i) => i + 1).join('\n')
    const chunks = [...parseNewlineDelimitedNumbers(many)]
    expect(chunks).toHaveLength(2)
    expect(chunks[0]).toHaveLength(1000)
    expect(chunks[0][0]).toBe(1)
    expect(chunks[0][999]).toBe(1000)
    expect(chunks[1]).toHaveLength(1)
    expect(chunks[1][0]).toBe(1001)
  })
})

describe('buildGetExternalStreams', () => {
  let originalFetch: typeof globalThis.fetch

  beforeEach(() => {
    mockRequestCreateStreamInput.mockReset()
    mockSendStreamChunk.mockReset()
    mockCloseStream.mockReset()
    if (originalFetch === undefined) {
      originalFetch = globalThis.fetch
    }
    vi.stubGlobal('fetch', vi.fn())
  })

  afterEach(() => {
    if (originalFetch !== undefined) {
      vi.stubGlobal('fetch', originalFetch)
    }
  })

  it('getter returns {} when target node has no inputs', async () => {
    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'target',
          position: { x: 0, y: 0 },
          type: 'computation',
          uri: 'snaq://graph/t.sl',
          inputs: undefined,
        },
      ],
      () => [{ sourceId: 'f1', targetId: 'target', targetInputIndex: 0 }],
    )
    expect(getter).toBeDefined()
    const result = await getter!()
    expect(result).toEqual({})
  })

  it('getter returns {} when there are no file edges', async () => {
    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'target',
          position: { x: 0, y: 0 },
          type: 'computation',
          uri: 'snaq://graph/t.sl',
          inputs: [{ name: 'x', type: 'Vector' }],
        },
      ],
      () => [],
    )
    const result = await getter!()
    expect(result).toEqual({})
  })

  it('getter returns {} when target node is missing', async () => {
    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'f1',
          position: { x: 0, y: 0 },
          type: 'file' as const,
          uri: 'snaq://graph/f1.sl',
          url: 'https://example.com/d.txt',
        },
      ],
      () => [{ sourceId: 'f1', targetId: 'target', targetInputIndex: 0 }],
    )
    const result = await getter!()
    expect(result).toEqual({})
  })

  it('getter skips file edge when source has no url', async () => {
    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'f1',
          position: { x: 0, y: 0 },
          type: 'file' as const,
          uri: 'snaq://graph/f1.sl',
          url: undefined,
        },
        {
          id: 'target',
          position: { x: 100, y: 0 },
          type: 'computation',
          uri: 'snaq://graph/t.sl',
          inputs: [{ name: 'x', type: 'Vector' }],
        },
      ],
      () => [{ sourceId: 'f1', targetId: 'target', targetInputIndex: 0 }],
    )
    const result = await getter!()
    expect(result).toEqual({})
    expect(mockRequestCreateStreamInput).not.toHaveBeenCalled()
  })

  it('getter skips edge when target input name is empty', async () => {
    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'f1',
          position: { x: 0, y: 0 },
          type: 'file' as const,
          uri: 'snaq://graph/f1.sl',
          url: 'https://example.com/d.txt',
        },
        {
          id: 'target',
          position: { x: 100, y: 0 },
          type: 'computation',
          uri: 'snaq://graph/t.sl',
          inputs: [{ name: '  ', type: 'Vector' }],
        },
      ],
      () => [{ sourceId: 'f1', targetId: 'target', targetInputIndex: 0 }],
    )
    const result = await getter!()
    expect(result).toEqual({})
    expect(mockRequestCreateStreamInput).not.toHaveBeenCalled()
  })

  it('getter returns name → index and feeds stream when one file edge with url', async () => {
    mockRequestCreateStreamInput.mockResolvedValue(0)
    const fetchMock = vi.mocked(globalThis.fetch)
    fetchMock.mockResolvedValue({
      ok: true,
      text: () => Promise.resolve('1\n2\n3'),
    } as Response)

    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'f1',
          position: { x: 0, y: 0 },
          type: 'file' as const,
          uri: 'snaq://graph/f1.sl',
          url: 'https://example.com/d.txt',
        },
        {
          id: 'target',
          position: { x: 100, y: 0 },
          type: 'computation',
          uri: 'snaq://graph/t.sl',
          inputs: [{ name: 'x', type: 'Vector' }],
        },
      ],
      () => [{ sourceId: 'f1', targetId: 'target', targetInputIndex: 0 }],
    )

    const result = await getter!()
    expect(result).toEqual({ x: 0 })
    expect(mockRequestCreateStreamInput).toHaveBeenCalledTimes(1)
    expect(mockSendStreamChunk).toHaveBeenCalledWith(0, [1, 2, 3])
    expect(mockCloseStream).toHaveBeenCalledWith(0)
  })

  it('getter catches fetch failure and skips that input, returns partial result', async () => {
    const consoleSpy = vi.spyOn(console, 'error').mockImplementation(() => {})
    mockRequestCreateStreamInput.mockResolvedValueOnce(0).mockResolvedValueOnce(1)
    const fetchMock = vi.mocked(globalThis.fetch)
    fetchMock
      .mockRejectedValueOnce(new Error('Network error'))
      .mockResolvedValueOnce({
        ok: true,
        text: () => Promise.resolve('4\n5'),
      } as Response)

    const getter = buildGetExternalStreams(
      'target',
      () => [
        {
          id: 'f1',
          position: { x: 0, y: 0 },
          type: 'file' as const,
          uri: 'snaq://graph/f1.sl',
          url: 'https://example.com/bad.txt',
        },
        {
          id: 'f2',
          position: { x: 50, y: 0 },
          type: 'file' as const,
          uri: 'snaq://graph/f2.sl',
          url: 'https://example.com/good.txt',
        },
        {
          id: 'target',
          position: { x: 100, y: 0 },
          type: 'computation',
          uri: 'snaq://graph/t.sl',
          inputs: [
            { name: 'a', type: 'Vector' },
            { name: 'b', type: 'Vector' },
          ],
        },
      ],
      () => [
        { sourceId: 'f1', targetId: 'target', targetInputIndex: 0 },
        { sourceId: 'f2', targetId: 'target', targetInputIndex: 1 },
      ],
    )

    const result = await getter!()
    expect(result).toEqual({ b: 1 })
    expect(consoleSpy).toHaveBeenCalledWith(
      '[buildGetExternalStreams] feed failed for',
      'a',
      expect.any(Error),
    )
    consoleSpy.mockRestore()
  })
})
