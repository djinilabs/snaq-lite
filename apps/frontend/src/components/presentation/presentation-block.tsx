/**
 * When wired (sourceUri non-empty): subscribes via subscribeWidget on mount, unsubscribes on unmount.
 * When not wired (sourceUri empty): does not subscribe; shows placeholder.
 * Consumes widgetDataUpdate for this widgetId via widget store; renders WidgetDataView when wired.
 * The LSP pushes updated results when the source computation changes (no re-subscribe).
 */

import { useRef } from 'react'
import { generateWidgetId } from '~/lib/utils'
import { useSubscribeWidget } from '~/hooks/use-subscribe-widget'
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
  const isWired = sourceUri.trim() !== ''

  useSubscribeWidget({ widgetId, sourceUri, enabled: isWired })

  return (
    <div style={{ padding: 4, minHeight: 40 }}>
      {isWired ? (
        <WidgetDataView state={state} />
      ) : (
        <span style={{ color: 'var(--text-muted)' }}>{PLACEHOLDER_UNWIRED}</span>
      )}
    </div>
  )
}
