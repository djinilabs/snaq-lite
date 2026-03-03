/**
 * Build getExternalStreams for subscribeWidget when the node has inputs wired from file blocks.
 * Creates streams via worker, feeds with newline-delimited numbers from file URL, returns input name → stream index.
 */

import type { GraphEdge, GraphNode } from '~/store'
import { requestCreateStreamInput, sendStreamChunk, closeStream } from '~/lsp/message-router'

const BATCH_SIZE = 1000

/** Parse text as newline-delimited numbers; yields batches of numbers. Exported for unit tests. */
export function* parseNewlineDelimitedNumbers(text: string): Generator<number[]> {
  const lines = text.split(/\r?\n/)
  let batch: number[] = []
  for (const line of lines) {
    const trimmed = line.trim()
    if (trimmed === '') continue
    const n = Number(trimmed)
    if (!Number.isFinite(n)) continue
    batch.push(n)
    if (batch.length >= BATCH_SIZE) {
      yield batch
      batch = []
    }
  }
  if (batch.length > 0) yield batch
}

/**
 * Fetch URL (blob, data, or https), parse as newline-delimited numbers, push chunks to stream, then close.
 * Returns the stream index. On fetch/parse error throws.
 */
async function feedUrlToStream(url: string): Promise<number> {
  const index = await requestCreateStreamInput()
  try {
    const res = await fetch(url)
    if (!res.ok) throw new Error(`Fetch failed: ${res.status} ${res.statusText}`)
    const text = await res.text()
    for (const chunk of parseNewlineDelimitedNumbers(text)) {
      sendStreamChunk(index, chunk)
    }
  } finally {
    closeStream(index)
  }
  return index
}

/**
 * Build a getExternalStreams function for the given node.
 * When invoked, finds edges from file nodes to this node, creates and feeds one stream per file input, returns name → index.
 * Skips file edges with missing url; those inputs will be unbound (LSP may error or use default).
 */
export function buildGetExternalStreams(
  nodeId: string,
  getNodes: () => GraphNode[],
  getEdges: () => GraphEdge[],
): (() => Promise<Record<string, number>>) | undefined {
  return async (): Promise<Record<string, number>> => {
    const nodes = getNodes()
    const edges = getEdges()
    const targetNode = nodes.find((n) => n.id === nodeId)
    if (!targetNode?.inputs) return {}

    const fileEdges = edges.filter((e) => {
      if (e.targetId !== nodeId) return false
      const source = nodes.find((n) => n.id === e.sourceId)
      return source?.type === 'file'
    })
    if (fileEdges.length === 0) return {}

    const result: Record<string, number> = {}
    for (const edge of fileEdges) {
      const sourceNode = nodes.find((n) => n.id === edge.sourceId)
      const inputName = targetNode.inputs?.[edge.targetInputIndex]?.name
      if (!sourceNode || !inputName?.trim()) continue
      const url = sourceNode.url
      if (!url?.trim()) continue
      try {
        const index = await feedUrlToStream(url)
        result[inputName] = index
      } catch (e) {
        console.error('[buildGetExternalStreams] feed failed for', inputName, e)
        // Skip this input; LSP may see it as unbound
      }
    }
    return result
  }
}
