/**
 * When wired (sourceUri non-empty): subscribes via subscribeWidget on mount, unsubscribes on unmount.
 * When not wired (sourceUri empty): does not subscribe; shows placeholder.
 * Consumes widgetDataUpdate for this widgetId via widget store; renders WidgetDataView when wired.
 */

import { useEffect, useRef } from 'react'
import { getLanguageClient, hasLanguageClient } from '~/lsp/language-client-singleton'
import { LSP_METHOD_SUBSCRIBE_WIDGET, LSP_METHOD_UNSUBSCRIBE_WIDGET } from '~/lib/constants'
import { generateWidgetId } from '~/lib/utils'
import { useWidgetStore } from '~/store'
import { WidgetDataView } from './widget-data-view'

interface PresentationBlockProps {
  sourceUri: string
  /** Optional: use when parent needs to pass a stable id (e.g. node id); otherwise a UUID is generated. */
  widgetId?: string
}

const PLACEHOLDER_UNWIRED = 'Connect a computation box'

export function PresentationBlock({ sourceUri, widgetId: widgetIdProp }: PresentationBlockProps) {
  const generatedId = useRef<string>(generateWidgetId()).current
  const widgetId = widgetIdProp ?? generatedId
  const state = useWidgetStore((s) => s.byId[widgetId])
  const removeWidget = useWidgetStore((s) => s.removeWidget)
  const isWired = sourceUri.trim() !== ''

  useEffect(() => {
    if (!isWired) return () => {}

    let didSubscribe = false
    const maxWaitMs = 10_000
    const intervalMs = 200
    const deadline = Date.now() + maxWaitMs
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
      }, intervalMs)
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
  }, [widgetId, sourceUri, isWired, removeWidget])

  return (
    <div style={{ padding: 4, minHeight: 40 }}>
      {isWired ? (
        <WidgetDataView state={state} />
      ) : (
        <span style={{ color: '#888' }}>{PLACEHOLDER_UNWIRED}</span>
      )}
    </div>
  )
}
