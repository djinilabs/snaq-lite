/**
 * On mount: generates a UUID (widgetId), then subscribeWidget({ widgetId, sourceUri }).
 * On unmount: unsubscribeWidget({ widgetId }) in useEffect cleanup.
 * Consumes widgetDataUpdate for this widgetId via widget store; renders WidgetDataView.
 */

import { useEffect, useRef } from 'react'
import { request } from '~/lsp'
import { LSP_METHOD_SUBSCRIBE_WIDGET, LSP_METHOD_UNSUBSCRIBE_WIDGET } from '~/lib/constants'
import { generateWidgetId } from '~/lib/utils'
import { useWidgetStore } from '~/store'
import { WidgetDataView } from './widget-data-view'

interface PresentationBlockProps {
  sourceUri: string
  /** Optional: use when parent needs to pass a stable id (e.g. node id); otherwise a UUID is generated. */
  widgetId?: string
}

export function PresentationBlock({ sourceUri, widgetId: widgetIdProp }: PresentationBlockProps) {
  const generatedId = useRef<string>(generateWidgetId()).current
  const widgetId = widgetIdProp ?? generatedId
  const state = useWidgetStore((s) => s.byId[widgetId])
  const removeWidget = useWidgetStore((s) => s.removeWidget)

  useEffect(() => {
    request(LSP_METHOD_SUBSCRIBE_WIDGET, { widgetId, sourceUri }).catch(() => {})
    return () => {
      request(LSP_METHOD_UNSUBSCRIBE_WIDGET, { widgetId }).catch(() => {})
      removeWidget(widgetId)
    }
  }, [widgetId, sourceUri, removeWidget])

  return (
    <div style={{ padding: 4, minHeight: 40 }}>
      <WidgetDataView state={state} />
    </div>
  )
}
