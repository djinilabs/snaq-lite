/**
 * Initializes LSP worker and registers message router handlers for graph and widget updates.
 * Mount once at app root.
 */

import { useEffect } from 'react'
import { initLspClient, setMessageRouterHandlers } from '~/lsp'
import { useGraphStore } from '~/store'
import { useWidgetStore } from '~/store'

export function LspProvider({ children }: { children: React.ReactNode }) {
  useEffect(() => {
    const workerUrl = new URL('../worker/lsp.worker.ts', import.meta.url)
    initLspClient(workerUrl)
    setMessageRouterHandlers({
      onNodeSignatureUpdated: (params) => {
        useGraphStore.getState().applyNodeSignature(
          params.uri,
          params.inputs,
          params.outputType ?? null,
        )
      },
      onWidgetDataUpdate: (params) => {
        useWidgetStore.getState().setWidget(params.widgetId, {
          status: params.status,
          payload: params.payload,
        })
      },
    })
  }, [])
  return <>{children}</>
}
