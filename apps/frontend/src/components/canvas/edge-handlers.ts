/**
 * Logic to send snaqlite/graph/connect and disconnect via LSP client and update graph store.
 */

import { getModel } from '~/editor/text-model-registry'
import { buildComputationDocumentContent } from '~/lib/computation-document-content'
import {
  COMPUTATION_OUTPUT_HANDLE_RIGHT,
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

/** Full document content for a computation target (input decls + body) for LSP didOpen. */
function computationDocumentContent(
  targetUri: string,
  targetNode: { inputs?: { name: string; type: string }[]; initialContent?: string },
): string {
  const body = getModel(targetUri, undefined as never)?.getValue() ?? targetNode.initialContent ?? ''
  return buildComputationDocumentContent(body, targetNode.inputs)
}

function errorMessage(e: unknown): string {
  return e instanceof Error ? e.message : String(e)
}

const LSP_WAIT_MS = 15_000

/**
 * Optimistic connect: add edge to store and draw wire immediately, then send LSP connect.
 * targetInputIndex is the 0-based index of the target node's input port (connection survives renames).
 * sourceHandle is which output port the edge is drawn from (right, top, or bottom).
 * LSP is called with the current input name at that index.
 */
export async function connectEdge(
  sourceUri: string,
  targetUri: string,
  targetInputIndex: number,
  sourceHandle?: string,
): Promise<boolean> {
  const state = useGraphStore.getState()
  const sourceNode = state.nodes.find((n) => n.uri === sourceUri)
  const sourceId = sourceNode?.id
  const targetId = state.nodes.find((n) => n.uri === targetUri)?.id
  if (!sourceId || !targetId) return false

  const targetNode = state.nodes.find((n) => n.id === targetId)
  const targetInputName = targetNode?.inputs?.[targetInputIndex]?.name
  if (targetInputName == null || targetInputName.trim() === '') {
    useUIStore.getState().addToast('Target input not found or has no name.', 'error')
    return false
  }

  if (sourceNode?.type === 'file') {
    useGraphStore.getState().addEdge({
      sourceId,
      targetId,
      targetInputIndex,
      sourceHandle: sourceHandle ?? COMPUTATION_OUTPUT_HANDLE_RIGHT,
    })
    if (targetNode?.type === 'computation') {
      useWidgetContentVersionStore.getState().increment(`${COMPUTATION_RESULT_WIDGET_ID_PREFIX}${targetId}`)
    }
    return true
  }

  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) {
    useUIStore.getState().addToast('Editor is still loading. Please try again in a moment.', 'error')
    return false
  }
  // Ensure LSP has latest source document (e.g. "4") so run_node_with_graph_inputs gets correct upstream value.
  if (sourceNode?.type === 'computation') {
    const sourceContent = computationDocumentContent(sourceUri, sourceNode)
    if (sourceContent.trim().length > 0) {
      langClient.sendNotification(LSP_METHOD_DID_OPEN, {
        textDocument: { uri: sourceUri, version: 1, languageId: 'snaq', text: sourceContent },
      })
    }
  }
  if (targetNode?.type === 'presentation') {
    const content = presentationDocumentContent(targetNode.inputs)
    langClient.sendNotification(LSP_METHOD_DID_OPEN, {
      textDocument: { uri: targetUri, version: 1, languageId: 'snaq', text: content },
    })
    await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))
  }
  // Do not send didOpen for computation target: LSP did_open invalidates widgets for that URI,
  // so refresh_widgets_for_uri would then find no subscribers and never push the bound result.
  // Target document is already open from the node's subscribeWidget; editor sends didChange on edit.

  try {
    await langClient.sendRequest(LSP_METHOD_GRAPH_CONNECT, {
      sourceUri,
      targetUri,
      targetInputName,
    })
    useGraphStore.getState().addEdge({
      sourceId,
      targetId,
      targetInputIndex,
      sourceHandle: sourceHandle ?? COMPUTATION_OUTPUT_HANDLE_RIGHT,
    })
    // Do not increment widget content version here: LSP refresh_widgets_for_uri already pushes
    // the new result to subscribed widgets. Incrementing would trigger re-subscribe (effect
    // cleanup → removeWidget + unsubscribe) and race with the incoming widgetDataUpdate.
    return true
  } catch (e) {
    useGraphStore.getState().clearPendingEdge()
    useUIStore.getState().addToast(errorMessage(e), 'error')
    return false
  }
}

/**
 * Optimistic disconnect: remove edge from store first (UI updates immediately), then notify LSP.
 * targetInputIndex is the 0-based index of the target's input; LSP is called with current name at that index.
 */
export async function disconnectEdge(
  targetUri: string,
  targetInputIndex: number,
): Promise<void> {
  const state = useGraphStore.getState()
  const targetId = state.nodes.find((n) => n.uri === targetUri)?.id
  if (!targetId) return

  const edge = state.edges.find(
    (e) => e.targetId === targetId && e.targetInputIndex === targetInputIndex,
  )
  const sourceId = edge?.sourceId
  const sourceNode = sourceId != null ? state.nodes.find((n) => n.id === sourceId) : undefined
  const targetNode = state.nodes.find((n) => n.id === targetId)
  const targetInputName = targetNode?.inputs?.[targetInputIndex]?.name ?? ''

  state.removeEdge(targetId, targetInputIndex)

  if (sourceNode?.type === 'file') return

  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) return

  try {
    await langClient.sendRequest(LSP_METHOD_GRAPH_DISCONNECT, {
      targetUri,
      targetInputName,
    })
  } catch (e) {
    if (sourceId != null) {
      useGraphStore.getState().addEdge({ sourceId, targetId, targetInputIndex })
    }
    useUIStore.getState().addToast(errorMessage(e), 'error')
  }
}

/**
 * Re-syncs all incoming edges for a node to the LSP with the node's current input names.
 * Call after setNodeInputs so the LSP graph binding updates (e.g. after renaming an input
 * from "x" to "abc", the LSP must receive graph/connect with targetInputName "abc").
 * Sends didOpen for the target so the LSP has the latest document, then graph/connect per edge.
 */
export async function syncIncomingEdgesToLsp(targetId: string): Promise<void> {
  const langClient = await waitForLanguageClient(LSP_WAIT_MS)
  if (!langClient) return

  const state = useGraphStore.getState()
  const incoming = state.edges.filter((e) => e.targetId === targetId)
  if (incoming.length === 0) return

  const targetNode = state.nodes.find((n) => n.id === targetId)
  if (!targetNode?.uri) return

  const targetUri = targetNode.uri
  if (targetNode.type === 'presentation') {
    const content = presentationDocumentContent(targetNode.inputs)
    langClient.sendNotification(LSP_METHOD_DID_OPEN, {
      textDocument: { uri: targetUri, version: 1, languageId: 'snaq', text: content },
    })
  } else if (targetNode.type === 'computation') {
    const content = computationDocumentContent(targetUri, targetNode)
    if (content.trim().length > 0) {
      langClient.sendNotification(LSP_METHOD_DID_OPEN, {
        textDocument: { uri: targetUri, version: 1, languageId: 'snaq', text: content },
      })
    }
  }

  await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))

  const nodes = state.nodes
  for (const edge of incoming) {
    const sourceNode = nodes.find((n) => n.id === edge.sourceId)
    if (sourceNode?.type === 'file') continue
    const targetInputName = targetNode.inputs?.[edge.targetInputIndex]?.name
    if (
      sourceNode?.uri &&
      targetInputName != null &&
      targetInputName.trim() !== ''
    ) {
      try {
        await langClient.sendRequest(LSP_METHOD_GRAPH_CONNECT, {
          sourceUri: sourceNode.uri,
          targetUri,
          targetInputName,
        })
      } catch {
        // Per-edge errors (e.g. type mismatch) not surfaced to user on re-sync
      }
    }
  }

  if (targetNode.type === 'computation') {
    useWidgetContentVersionStore.getState().increment(`${COMPUTATION_RESULT_WIDGET_ID_PREFIX}${targetId}`)
  }
}
