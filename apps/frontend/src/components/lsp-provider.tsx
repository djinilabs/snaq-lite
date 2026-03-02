/**
 * Initializes LSP worker and registers message router handlers for graph and widget updates.
 * After the worker is ready, creates the LSP connection (MessageConnection), runs the
 * initialize handshake, and sets the language client singleton for sendRequest/sendNotification.
 * Mount once at app root.
 */

import { useEffect, useRef } from 'react'
import {
  initLspClient,
  setMessageRouterHandlers,
  waitForWorkerReady,
  createLspConnection,
  sendToWorker,
  setIncomingLspPush,
} from '~/lsp'
import { setLanguageClient } from '~/lsp/language-client-singleton'
// Vite bundles the worker and resolves this to a URL that works in dev and production
import lspWorkerUrl from '../worker/lsp.worker.ts?worker&url'
import { disposeModel } from '~/editor/text-model-registry'
import { nodeIdToUri } from '~/editor/virtual-uri'
import { getRemovedNodeIds } from '~/editor/model-lifecycle'
import { applyDiagnosticsToMonaco } from '~/editor/apply-diagnostics'
import { useGraphStore } from '~/store'
import { useWidgetStore } from '~/store'

const INITIALIZE_PARAMS = {
  processId: null as number | null,
  rootUri: null as string | null,
  capabilities: {},
  clientInfo: { name: 'snaq-lite-frontend', version: '0.0.0' },
}

export function LspProvider({ children }: { children: React.ReactNode }) {
  useEffect(() => {
    const base = (import.meta.env.BASE_URL ?? '/').replace(/\/?$/, '/')
    const wasmUrl = `${window.location.origin}${base}lsp-wasm/snaq_lite_lsp.js`
    initLspClient(lspWorkerUrl, wasmUrl)
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
      onPublishDiagnostics: applyDiagnosticsToMonaco,
    })

    async function startConnection(): Promise<void> {
      try {
        await waitForWorkerReady()
        const { connection, push } = createLspConnection(sendToWorker)
        connection.listen()
        setIncomingLspPush(push)
        await connection.sendRequest('initialize', INITIALIZE_PARAMS)
        connection.sendNotification('initialized', {})
        setLanguageClient({
          sendRequest: (method, params) => connection.sendRequest(method, params),
          sendNotification: (method, params) => {
            void connection.sendNotification(method, params)
          },
        })
      } catch (err) {
        console.error('[LSP] Failed to start connection:', err)
      }
    }

    void startConnection()
  }, [])

  // When a node is removed from the graph, dispose its text model so the registry does not leak.
  const nodes = useGraphStore((s) => s.nodes)
  const prevNodeIdsRef = useRef<Set<string>>(new Set())
  useEffect(() => {
    const removed = getRemovedNodeIds(prevNodeIdsRef.current, nodes)
    for (const id of removed) {
      disposeModel(nodeIdToUri(id))
    }
    prevNodeIdsRef.current = new Set(nodes.map((n) => n.id))
  }, [nodes])

  return <>{children}</>
}
