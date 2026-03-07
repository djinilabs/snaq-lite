/**
 * Tests for useSubscribeWidget: onBeforeSubscribe called before subscribeWidget,
 * subscribeKey triggers re-subscribe (unsubscribe then subscribe).
 */

import { describe, it, expect, beforeEach, vi } from 'vitest'
import { act } from 'react'
import { createRoot } from 'react-dom/client'
import { useSubscribeWidget } from './use-subscribe-widget'
import {
  LSP_METHOD_SUBSCRIBE_WIDGET,
  LSP_METHOD_UNSUBSCRIBE_WIDGET,
  LSP_SUBSCRIBE_AFTER_DID_OPEN_MS,
} from '~/lib/constants'

const mockSendRequest = vi.fn()
const mockSendNotification = vi.fn()
const mockClient = {
  sendRequest: mockSendRequest,
  sendNotification: mockSendNotification,
}
vi.mock('~/lsp/language-client-singleton', () => ({
  whenLspReady: () => Promise.resolve(mockClient),
  getLanguageClient: () => mockClient,
  hasLanguageClient: () => true,
}))

const mockRemoveWidget = vi.fn()
vi.mock('~/store', () => ({
  useWidgetStore: (selector: (s: { removeWidget: () => void }) => unknown) =>
    selector({ removeWidget: mockRemoveWidget }),
}))

function renderWithHook(
  widgetId: string,
  sourceUri: string,
  options: { onBeforeSubscribe?: () => void; subscribeKey?: number } = {},
): { unmount: () => void } {
  function TestComponent() {
    useSubscribeWidget({
      widgetId,
      sourceUri,
      enabled: true,
      onBeforeSubscribe: options.onBeforeSubscribe,
      subscribeKey: options.subscribeKey,
    })
    return null
  }
  const container = document.createElement('div')
  document.body.appendChild(container)
  const root = createRoot(container)
  root.render(<TestComponent />)
  return {
    unmount: () => {
      root.unmount()
      document.body.removeChild(container)
    },
  }
}

describe('useSubscribeWidget', () => {
  beforeEach(() => {
    mockSendRequest.mockClear()
    mockSendNotification.mockClear()
    mockSendRequest.mockResolvedValue(undefined)
  })

  it('calls onBeforeSubscribe then sendRequest(SUBSCRIBE_WIDGET) after delay', async () => {
    vi.useFakeTimers()
    const callOrder: string[] = []
    const onBeforeSubscribe = () => {
      callOrder.push('onBeforeSubscribe')
    }
    mockSendRequest.mockImplementation(() => {
      callOrder.push('sendRequest')
      return Promise.resolve()
    })

    const { unmount } = renderWithHook('w1', 'snaq://graph/n1.sl', {
      onBeforeSubscribe,
    })
    await act(async () => {})
    expect(callOrder).toEqual(['onBeforeSubscribe'])

    await act(async () => {
      vi.advanceTimersByTime(LSP_SUBSCRIBE_AFTER_DID_OPEN_MS)
    })
    expect(callOrder).toEqual(['onBeforeSubscribe', 'sendRequest'])
    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.objectContaining({ widgetId: 'w1', sourceUri: 'snaq://graph/n1.sl' }),
    )
    unmount()
    vi.useRealTimers()
  })

  it('subscribes without calling onBeforeSubscribe when not provided', async () => {
    renderWithHook('w1', 'snaq://graph/n1.sl', {})
    await act(async () => {})

    expect(mockSendRequest).toHaveBeenCalledWith(
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.objectContaining({ widgetId: 'w1', sourceUri: 'snaq://graph/n1.sl' }),
    )
    expect(mockSendNotification).not.toHaveBeenCalled()
  })

  it('when subscribeKey changes, unsubscribes then subscribes again', async () => {
    function TestWithKey({ subscribeKey }: { subscribeKey: number }) {
      useSubscribeWidget({
        widgetId: 'w1',
        sourceUri: 'snaq://graph/n1.sl',
        enabled: true,
        subscribeKey,
      })
      return null
    }
    const container = document.createElement('div')
    document.body.appendChild(container)
    const root = createRoot(container)

    root.render(<TestWithKey subscribeKey={0} />)
    await act(async () => {})

    expect(mockSendRequest).toHaveBeenCalledTimes(1)
    expect(mockSendRequest).toHaveBeenNthCalledWith(
      1,
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.anything(),
    )
    mockSendRequest.mockClear()

    root.render(<TestWithKey subscribeKey={1} />)
    await act(async () => {})

    expect(mockSendRequest).toHaveBeenCalledTimes(2)
    expect(mockSendRequest).toHaveBeenNthCalledWith(
      1,
      LSP_METHOD_UNSUBSCRIBE_WIDGET,
      expect.objectContaining({ widgetId: 'w1' }),
    )
    expect(mockSendRequest).toHaveBeenNthCalledWith(
      2,
      LSP_METHOD_SUBSCRIBE_WIDGET,
      expect.objectContaining({ widgetId: 'w1', sourceUri: 'snaq://graph/n1.sl' }),
    )

    root.unmount()
    document.body.removeChild(container)
  })
})
