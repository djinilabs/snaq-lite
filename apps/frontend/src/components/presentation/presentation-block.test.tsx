import { describe, it, expect, beforeEach, vi } from 'vitest'
import type { ReactElement } from 'react'
import { act } from 'react'
import { createRoot } from 'react-dom/client'
import { PresentationBlock } from './presentation-block'
import {
  LSP_METHOD_SUBSCRIBE_WIDGET,
  LSP_METHOD_UNSUBSCRIBE_WIDGET,
} from '~/lib/constants'

const mockSendRequest = vi.fn()
vi.mock('~/lsp/language-client-singleton', () => ({
  getLanguageClient: () => ({
    sendRequest: mockSendRequest,
  }),
  hasLanguageClient: () => true,
}))

function render(ui: ReactElement): { unmount: () => void } {
  const container = document.createElement('div')
  document.body.appendChild(container)
  const root = createRoot(container)
  root.render(ui)
  return {
    unmount: () => {
      root.unmount()
      document.body.removeChild(container)
    },
  }
}

describe('PresentationBlock', () => {
  beforeEach(() => {
    mockSendRequest.mockClear()
  })

  it('does not call subscribeWidget when sourceUri is empty', () => {
    const { unmount } = render(<PresentationBlock sourceUri="" />)
    expect(mockSendRequest).not.toHaveBeenCalledWith(
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.anything(),
    )
    unmount()
  })

  it('does not call subscribeWidget when sourceUri is only whitespace', () => {
    const { unmount } = render(<PresentationBlock sourceUri="   " />)
    expect(mockSendRequest).not.toHaveBeenCalledWith(
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.anything(),
    )
    unmount()
  })

  it('calls subscribeWidget with widgetId and sourceUri when sourceUri is non-empty', async () => {
    const sourceUri = 'snaq://graph/comp-1.sl'
    mockSendRequest.mockResolvedValue(undefined)
    const { unmount } = render(<PresentationBlock sourceUri={sourceUri} />)
    await act(async () => {})
    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.objectContaining({
        sourceUri,
      }),
    )
    const call = mockSendRequest.mock.calls.find(
      (c) => c[0] === LSP_METHOD_SUBSCRIBE_WIDGET,
    )
    expect(call?.[1]).toHaveProperty('widgetId')
    expect(typeof call?.[1].widgetId).toBe('string')
    expect(call?.[1].widgetId.length).toBeGreaterThan(0)
    unmount()
  })

  it('calls unsubscribeWidget on unmount when subscribed', async () => {
    const sourceUri = 'snaq://graph/comp-1.sl'
    mockSendRequest.mockResolvedValue(undefined)
    const { unmount } = render(<PresentationBlock sourceUri={sourceUri} />)
    await act(async () => {})
    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.anything(),
    )
    const subscribeCall = mockSendRequest.mock.calls.find(
      (c) => c[0] === LSP_METHOD_SUBSCRIBE_WIDGET,
    )
    const widgetId = subscribeCall?.[1].widgetId
    mockSendRequest.mockClear()
    unmount()
    await act(async () => {})
    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_UNSUBSCRIBE_WIDGET,
      { widgetId },
    )
  })
})
