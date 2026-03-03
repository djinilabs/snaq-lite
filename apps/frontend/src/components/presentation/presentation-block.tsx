/**
 * When wired (sourceUri non-empty): subscribes via subscribeWidget on mount, unsubscribes on unmount.
 * When not wired (sourceUri empty): does not subscribe; shows placeholder.
 * Consumes widgetDataUpdate for this widgetId via widget store; renders WidgetDataView when wired.
 * The LSP pushes updated results when the source computation changes (no re-subscribe).
 *
 * Must subscribe with documentUri (this block's document), not the computation's URI, so the LSP
 * registers the widget under the presentation URI and refresh_downstream_widgets finds it when the source changes.
 */

import { useRef } from 'react'
import { generateWidgetId } from '~/lib/utils'
import { useSubscribeWidget } from '~/hooks/use-subscribe-widget'
import { useWidgetStore } from '~/store'
import { WidgetDataView } from './widget-data-view'

interface PresentationBlockProps {
  /** When non-empty, this block is wired (edge from computation); used only for isWired. */
  sourceUri: string
  /** URI of the document to run and subscribe to (this presentation node's URI). Required when wired so the LSP registers the widget under this URI and can push updates when the source computation changes. */
  documentUri: string
  /** Optional: use when parent needs to pass a stable id (e.g. node id); otherwise a UUID is generated. */
  widgetId?: string
  /** Called immediately before subscribeWidget so the LSP has the document open (avoids "source document not open" after refresh). */
  onBeforeSubscribe?: () => void
  /** When present, used to feed file-block streams before subscribeWidget. */
  getExternalStreams?: () => Promise<Record<string, number>>
}

const PLACEHOLDER_UNWIRED = 'Connect a computation box'

export function PresentationBlock({
  sourceUri,
  documentUri,
  widgetId: widgetIdProp,
  onBeforeSubscribe,
  getExternalStreams,
}: PresentationBlockProps) {
  const generatedId = useRef<string>(generateWidgetId()).current
  const widgetId = widgetIdProp ?? generatedId
  const state = useWidgetStore((s) => s.byId[widgetId])
  const isWired = sourceUri.trim() !== ''

  useSubscribeWidget({
    widgetId,
    sourceUri: documentUri,
    enabled: isWired,
    onBeforeSubscribe,
    getExternalStreams,
  })

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
