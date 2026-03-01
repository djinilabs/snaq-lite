/**
 * Subscribes to widget result via LSP subscribeWidget when enabled.
 * Retries every LSP_SUBSCRIBE_RETRY_INTERVAL_MS until client is ready (max LSP_SUBSCRIBE_MAX_WAIT_MS).
 * On unmount or when enabled becomes false: unsubscribe and remove widget state.
 */

import { useEffect } from 'react'
import { getLanguageClient, hasLanguageClient } from '~/lsp/language-client-singleton'
import {
  LSP_METHOD_SUBSCRIBE_WIDGET,
  LSP_METHOD_UNSUBSCRIBE_WIDGET,
  LSP_SUBSCRIBE_RETRY_INTERVAL_MS,
  LSP_SUBSCRIBE_MAX_WAIT_MS,
} from '~/lib/constants'
import { useWidgetStore } from '~/store'

export interface UseSubscribeWidgetParams {
  widgetId: string
  sourceUri: string
  enabled: boolean
}

export function useSubscribeWidget({
  widgetId,
  sourceUri,
  enabled,
}: UseSubscribeWidgetParams): void {
  const removeWidget = useWidgetStore((s) => s.removeWidget)

  useEffect(() => {
    if (!enabled) return

    let didSubscribe = false
    const deadline = Date.now() + LSP_SUBSCRIBE_MAX_WAIT_MS
    let intervalId: ReturnType<typeof setInterval> | null = null

    function subscribe(): void {
      if (!hasLanguageClient()) return
      didSubscribe = true
      getLanguageClient()
        .sendRequest(LSP_METHOD_SUBSCRIBE_WIDGET, { widgetId, sourceUri })
        .catch(() => {})
    }

    if (hasLanguageClient()) {
      subscribe()
    } else {
      intervalId = setInterval(() => {
        if (didSubscribe || Date.now() >= deadline) {
          if (intervalId != null) clearInterval(intervalId)
          intervalId = null
          return
        }
        subscribe()
      }, LSP_SUBSCRIBE_RETRY_INTERVAL_MS)
    }

    return () => {
      if (intervalId != null) clearInterval(intervalId)
      removeWidget(widgetId)
      if (didSubscribe && hasLanguageClient()) {
        getLanguageClient()
          .sendRequest(LSP_METHOD_UNSUBSCRIBE_WIDGET, { widgetId })
          .catch(() => {})
      }
    }
  }, [widgetId, sourceUri, enabled, removeWidget])
}
