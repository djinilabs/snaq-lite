/**
 * Logic to send snaqlite/graph/connect and disconnect via LSP client and update graph store.
 */

import { getModel } from '~/editor/text-model-registry'
import {
  DEFAULT_PRESENTATION_DOCUMENT_CONTENT,
  LSP_METHOD_DID_OPEN,
  LSP_METHOD_GRAPH_CONNECT,
  LSP_METHOD_GRAPH_DISCONNECT,
  LSP_SUBSCRIBE_AFTER_DID_OPEN_MS,
} from '~/lib/constants'
import { waitForLanguageClient } from '~/lsp/language-client-singleton'
import { useGraphStore, useWidgetContentVersionStore } from '~/store'
import { useUIStore } from '~/store'

const COMPUTATION_RESULT_WIDGET_ID_PREFIX = 'computation-result-'

function presentationDocumentContent(inputs: { name: string; type: string }[] | undefined): string {
  if (!inputs?.length) return DEFAULT_PRESENTATION_DOCUMENT_CONTENT
  return inputs.map((i) => `input ${i.name}: ${i.type}\n$${i.name}`).join('\n')
}

/** Build document content for a computation target so the LSP has input decls (from UI) + body (from editor/store). */
function computationDocumentContent(
  targetUri: string,
  targetNode: { inputs?: { name: string; type: string }[]; initialContent?: string },
): string {
  const body = getModel(targetUri, undefined as never)?.getValue() ?? targetNode.initialContent ?? ''
  const inputDecls =
    targetNode.inputs
      ?.filter((i) => i.name.trim().length > 0)
      .map((i) => `input ${i.name}: ${i.type}`)
      .join('\n') ?? ''
  if (inputDecls.length === 0) return body
  return body.trimStart().startsWith('input ')
    ? body
    : `${inputDecls}\n${body}`.trim()
}

function errorMessage(e: unknown): string {
  return e instanceof Error ? e.message : String(e)
}

const LSP_WAIT_MS = 15_000

/**
 * Optimistic connect: add edge to store and draw wire immediately, then send LSP connect.
 * If the LSP is not ready yet, waits up to LSP_WAIT_MS for it before connecting.
 * On LSP error, drop the pending wire from the store and show error toast.
 */
export async function connectEdge(
  sourceUri: string,
  targetUri: string,
  targetInputName: string,
): Promise<boolean> {
  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) {
    useUIStore.getState().addToast('Editor is still loading. Please try again in a moment.', 'error')
    return false
  }
  const sourceId = useGraphStore.getState().nodes.find((n) => n.uri === sourceUri)?.id
  const targetId = useGraphStore.getState().nodes.find((n) => n.uri === targetUri)?.id
  if (!sourceId || !targetId) return false

  const targetNode = useGraphStore.getState().nodes.find((n) => n.id === targetId)
  if (targetNode?.type === 'presentation') {
    const content = presentationDocumentContent(targetNode.inputs)
    langClient.sendNotification(LSP_METHOD_DID_OPEN, {
      textDocument: { uri: targetUri, version: 1, languageId: 'snaq', text: content },
    })
    await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))
  } else if (targetNode?.type === 'computation') {
    let content = computationDocumentContent(targetUri, targetNode)
    // Ensure LSP has the target input: if content is empty but store has the input (e.g. UI-only), send minimal decl
    if (content.trim().length === 0) {
      const decl = targetNode.inputs?.find((i) => i.name.trim() && i.name === targetInputName)
      if (decl) content = `input ${decl.name}: ${decl.type}`
    }
    if (content.trim().length > 0) {
      langClient.sendNotification(LSP_METHOD_DID_OPEN, {
        textDocument: { uri: targetUri, version: 1, languageId: 'snaq', text: content },
      })
      await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))
    }
  }

  try {
    await langClient.sendRequest(LSP_METHOD_GRAPH_CONNECT, {
      sourceUri,
      targetUri,
      targetInputName,
    })
    useGraphStore.getState().addEdge({ sourceId, targetId, targetInputName })
    if (targetNode?.type === 'computation') {
      useWidgetContentVersionStore.getState().increment(`${COMPUTATION_RESULT_WIDGET_ID_PREFIX}${targetId}`)
    }
    return true
  } catch (e) {
    useGraphStore.getState().clearPendingEdge()
    useUIStore.getState().addToast(errorMessage(e), 'error')
    return false
  }
}

/**
 * Optimistic disconnect: remove edge from store, then notify LSP.
 * If the LSP is not ready yet, waits up to LSP_WAIT_MS for it.
 * On LSP error, re-add the edge (rollback) and show error toast.
 */
export async function disconnectEdge(
  targetUri: string,
  targetInputName: string,
): Promise<void> {
  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) {
    useUIStore.getState().addToast('Editor is still loading. Please try again in a moment.', 'error')
    return
  }
  const state = useGraphStore.getState()
  const targetId = state.nodes.find((n) => n.uri === targetUri)?.id
  if (!targetId) return

  const edge = state.edges.find(
    (e) => e.targetId === targetId && e.targetInputName === targetInputName,
  )
  const sourceId = edge?.sourceId

  state.removeEdge(targetId, targetInputName)
  try {
    await langClient.sendRequest(LSP_METHOD_GRAPH_DISCONNECT, {
      targetUri,
      targetInputName,
    })
  } catch (e) {
    if (sourceId != null) {
      useGraphStore.getState().addEdge({ sourceId, targetId, targetInputName })
    }
    useUIStore.getState().addToast(errorMessage(e), 'error')
  }
}
