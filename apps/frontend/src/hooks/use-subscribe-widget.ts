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
  LSP_SUBSCRIBE_AFTER_DID_OPEN_MS,
  LSP_SUBSCRIBE_RETRY_INTERVAL_MS,
  LSP_SUBSCRIBE_MAX_WAIT_MS,
} from '~/lib/constants'
import { useWidgetStore } from '~/store'

export interface UseSubscribeWidgetParams {
  widgetId: string
  sourceUri: string
  enabled: boolean
  /** Called immediately before each subscribeWidget request (e.g. to send didOpen). */
  onBeforeSubscribe?: () => void
  /** When present, called before subscribeWidget to create/feed file-block streams; result passed as externalStreams. */
  getExternalStreams?: () => Promise<Record<string, number>>
  /** When changed, effect re-runs: unsubscribe then subscribe (e.g. after content change). */
  subscribeKey?: number
}

export function useSubscribeWidget({
  widgetId,
  sourceUri,
  enabled,
  onBeforeSubscribe,
  getExternalStreams,
  subscribeKey,
}: UseSubscribeWidgetParams): void {
  const removeWidget = useWidgetStore((s) => s.removeWidget)

  useEffect(() => {
    if (!enabled) return

    let didSubscribe = false
    const deadline = Date.now() + LSP_SUBSCRIBE_MAX_WAIT_MS
    let intervalId: ReturnType<typeof setInterval> | null = null
    let deferTimeoutId: ReturnType<typeof setTimeout> | null = null

    function subscribe(): void {
      if (!hasLanguageClient()) return
      didSubscribe = true
      const doSubscribe = async (): Promise<void> => {
        deferTimeoutId = null
        if (!hasLanguageClient()) return
        try {
          // Resolve stream indices before didOpen so the worker processes createStreamInput
          // before any LSP work that can block the single thread (avoids response timeout).
          const externalStreams = await getExternalStreams?.().then((m) => m ?? undefined)
          try {
            onBeforeSubscribe?.()
          } catch (e) {
            console.error('[useSubscribeWidget] onBeforeSubscribe failed:', e)
          }
          if (onBeforeSubscribe != null) {
            await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))
          }
          const params: { widgetId: string; sourceUri: string; externalStreams?: Record<string, number> } = {
            widgetId,
            sourceUri,
          }
          if (externalStreams != null && Object.keys(externalStreams).length > 0) {
            params.externalStreams = externalStreams
          }
          await getLanguageClient().sendRequest(LSP_METHOD_SUBSCRIBE_WIDGET, params)
        } catch (err) {
          console.error('[useSubscribeWidget] subscribeWidget failed:', err)
        }
      }
      void doSubscribe()
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
      if (deferTimeoutId != null) clearTimeout(deferTimeoutId)
      if (intervalId != null) clearInterval(intervalId)
      removeWidget(widgetId)
      if (didSubscribe && hasLanguageClient()) {
        getLanguageClient()
          .sendRequest(LSP_METHOD_UNSUBSCRIBE_WIDGET, { widgetId })
          .catch(() => {})
      }
    }
  }, [widgetId, sourceUri, enabled, removeWidget, subscribeKey, onBeforeSubscribe, getExternalStreams])
}
