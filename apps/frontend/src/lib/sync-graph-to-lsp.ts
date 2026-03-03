/**
 * Syncs a loaded graph (nodes + edges) to the LSP so it has open documents and edges.
 * Call after setGraph when loading (typically in background). When sync completes and
 * graph/connect is sent for each edge, the LSP refreshes any already-subscribed
 * presentation widget so it receives the bound stream (fixes "unbound stream input"
 * after refresh).
 */

import { buildComputationDocumentContent } from '~/lib/computation-document-content'
import {
  DEFAULT_PRESENTATION_DOCUMENT_CONTENT,
  LSP_METHOD_DID_OPEN,
  LSP_METHOD_GRAPH_CONNECT,
  LSP_SUBSCRIBE_AFTER_DID_OPEN_MS,
} from '~/lib/constants'
import type { GraphEdge, GraphNode } from '~/store'
import type { LanguageClientLike } from '~/lsp/language-client-singleton'
import {
  getLanguageClient,
  waitForLanguageClient,
  whenClientReady,
} from '~/lsp/language-client-singleton'

/** Matches E2E "after full page refresh" assertion timeout; sync also runs when client becomes ready. */
const LSP_LOAD_SYNC_WAIT_MS = 25_000

/** When client is not ready in time, we register a callback; only the latest pending snapshot is synced when client becomes ready. */
let pendingSync: { nodes: GraphNode[]; edges: GraphEdge[] } | null = null

function presentationContent(inputs: { name: string; type: string }[] | undefined): string {
  if (!inputs?.length) return DEFAULT_PRESENTATION_DOCUMENT_CONTENT
  return inputs.map((i) => `input ${i.name}: ${i.type}\n$${i.name}`).join('\n')
}

function doSyncWithClient(
  client: LanguageClientLike,
  nodes: GraphNode[],
  edges: GraphEdge[],
): Promise<void> {
  for (const node of nodes) {
    if (node.type === 'file') continue
    const content =
      node.type === 'computation'
        ? buildComputationDocumentContent(node.initialContent ?? '', node.inputs)
        : presentationContent(node.inputs)
    client.sendNotification(LSP_METHOD_DID_OPEN, {
      textDocument: {
        uri: node.uri,
        version: 1,
        languageId: 'snaq',
        text: content,
      },
    })
  }
  return (async () => {
    await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))
    for (const edge of edges) {
      const sourceNode = nodes.find((n) => n.id === edge.sourceId)
      if (sourceNode?.type === 'file') continue
      const targetNode = nodes.find((n) => n.id === edge.targetId)
      const targetInputName = targetNode?.inputs?.[edge.targetInputIndex]?.name
      if (
        sourceNode?.uri &&
        targetNode?.uri &&
        targetInputName != null &&
        targetInputName.trim() !== ''
      ) {
        try {
          await client.sendRequest(LSP_METHOD_GRAPH_CONNECT, {
            sourceUri: sourceNode.uri,
            targetUri: targetNode.uri,
            targetInputName,
          })
        } catch {
          // Ignore per-edge errors (e.g. type mismatch on load)
        }
      }
    }
  })()
}

/**
 * Sends didOpen for each node and graph/connect for each edge so the LSP graph state
 * matches the loaded project. Call when loading a project (after setGraph).
 * If the client is not ready within the timeout, registers to run sync when it becomes
 * ready (fixes "unbound stream input" when LSP starts slowly after full page refresh).
 */
export async function syncLoadedGraphToLsp(
  nodes: GraphNode[],
  edges: GraphEdge[],
): Promise<void> {
  const client = await waitForLanguageClient(LSP_LOAD_SYNC_WAIT_MS)
  if (client) {
    await doSyncWithClient(client, nodes, edges)
    return
  }
  pendingSync = { nodes, edges }
  whenClientReady(() => {
    const p = pendingSync
    pendingSync = null
    if (p) {
      try {
        void doSyncWithClient(getLanguageClient(), p.nodes, p.edges)
      } catch {
        // Client not set (e.g. race); ignore
      }
    }
  })
}
