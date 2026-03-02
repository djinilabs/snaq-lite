/**
 * Syncs a loaded graph (nodes + edges) to the LSP so it has open documents and edges.
 * Call before setGraph when loading a project so the presentation block does not see
 * "unbound stream input" when it subscribes.
 */

import {
  DEFAULT_PRESENTATION_DOCUMENT_CONTENT,
  LSP_METHOD_DID_OPEN,
  LSP_METHOD_GRAPH_CONNECT,
  LSP_SUBSCRIBE_AFTER_DID_OPEN_MS,
} from '~/lib/constants'
import type { GraphEdge, GraphNode } from '~/store'
import { waitForLanguageClient } from '~/lsp/language-client-singleton'

const LSP_LOAD_SYNC_WAIT_MS = 8000

function presentationContent(inputs: { name: string; type: string }[] | undefined): string {
  if (!inputs?.length) return DEFAULT_PRESENTATION_DOCUMENT_CONTENT
  return inputs.map((i) => `input ${i.name}: ${i.type}\n$${i.name}`).join('\n')
}

/**
 * Sends didOpen for each node and graph/connect for each edge so the LSP graph state
 * matches the loaded project. Call when loading a project (before or when setting the graph).
 * Resolves when sync is done or when the client is not ready within the timeout.
 */
export async function syncLoadedGraphToLsp(
  nodes: GraphNode[],
  edges: GraphEdge[],
): Promise<void> {
  const client = await waitForLanguageClient(LSP_LOAD_SYNC_WAIT_MS)
  if (!client) return

  for (const node of nodes) {
    const content =
      node.type === 'computation'
        ? (node.initialContent ?? '')
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

  await new Promise((r) => setTimeout(r, LSP_SUBSCRIBE_AFTER_DID_OPEN_MS))

  for (const edge of edges) {
    const sourceNode = nodes.find((n) => n.id === edge.sourceId)
    const targetNode = nodes.find((n) => n.id === edge.targetId)
    if (sourceNode?.uri && targetNode?.uri) {
      try {
        await client.sendRequest(LSP_METHOD_GRAPH_CONNECT, {
          sourceUri: sourceNode.uri,
          targetUri: targetNode.uri,
          targetInputName: edge.targetInputName,
        })
      } catch {
        // Ignore per-edge errors (e.g. type mismatch on load)
      }
    }
  }
}
