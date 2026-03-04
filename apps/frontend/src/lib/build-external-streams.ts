/**
 * Build getExternalStreams for subscribeWidget when the node has inputs wired from file blocks.
 * Creates streams via worker, feeds from file URL (parse in JS, then pushChunk), returns input name → stream index.
 *
 * In the browser the WASM Host has no file access: it only receives chunks we push. The Host API's startFeeder
 * only parses newline-delimited numbers; for CSV the docs require "parse in JS and use pushChunk" (see
 * docs/EXTERNAL_STREAMS.md "WASM Host (browser)"). CSV/tabular parsing in Rust (snaq-lite-ingest) is used by
 * the CLI where the binary reads files from disk; here we parse in the frontend and push numeric chunks.
 *
 * For blob URLs we read from a cache (populated on file drop) to avoid fetch(blobUrl) which can fail in some environments.
 */

import type { GraphEdge, GraphNode } from '~/store'
import { useUIStore } from '~/store'
import { requestCreateStreamInput, sendStreamChunk, closeStream } from '~/lsp/message-router'
import { getBlobForUrl } from '~/lib/blob-url-cache'

const BATCH_SIZE = 1000

const UTF8_BOM = '\uFEFF'

/** Strip UTF-8 BOM from start of text so "10\\n20" with BOM still parses. Exported for unit tests. */
export function stripBom(text: string): string {
  return text.startsWith(UTF8_BOM) ? text.slice(UTF8_BOM.length) : text
}

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

/** CSV delimiter: comma or semicolon (semicolon common in European locales). */
const CSV_DELIMITER = /[,;]/

/**
 * Parse text as CSV: each line split by comma or semicolon, each cell trimmed and parsed as number; yields batches of numbers.
 * Skips non-finite cells. Exported for unit tests.
 */
export function* parseCsvToNumbers(text: string): Generator<number[]> {
  const lines = text.split(/\r?\n/)
  let batch: number[] = []
  for (const line of lines) {
    const cells = line.split(CSV_DELIMITER)
    for (const cell of cells) {
      const trimmed = cell.trim()
      if (trimmed === '') continue
      const n = Number(trimmed)
      if (!Number.isFinite(n)) continue
      batch.push(n)
      if (batch.length >= BATCH_SIZE) {
        yield batch
        batch = []
      }
    }
  }
  if (batch.length > 0) yield batch
}

/** Prefer CSV parser when fileType suggests CSV or when content has comma or semicolon in the first non-empty line. */
function chooseParser(text: string, fileType?: string): 'csv' | 'newline' {
  if (fileType?.toLowerCase().includes('csv')) return 'csv'
  const firstLine = text.split(/\r?\n/).find((l) => l.trim() !== '')
  if (firstLine?.includes(',') || firstLine?.includes(';')) return 'csv'
  return 'newline'
}

/**
 * Resolve URL to text: for blob URLs use in-memory cache (avoids fetch(blobUrl) which can fail).
 * Blob URLs not in cache (e.g. after page reload) throw a clear error instead of fetch.
 * For data: or https: use fetch.
 */
async function urlToText(url: string): Promise<string> {
  if (url.startsWith('blob:')) {
    const blob = getBlobForUrl(url)
    if (blob) return await blob.text()
    throw new Error(
      'File not available after reload. Blob URLs are only valid in the same session. Please re-drop the file.',
    )
  }
  const res = await fetch(url)
  if (!res.ok) throw new Error(`Fetch failed: ${res.status} ${res.statusText}`)
  return await res.text()
}

/**
 * Feed URL (blob, data, or https) to stream: resolve to text, parse (CSV or newline-delimited numbers), push chunks, close.
 * Uses CSV parsing when fileType is CSV or content looks like CSV; otherwise newline-delimited numbers.
 * Returns the stream index. On fetch/parse error throws.
 */
async function feedUrlToStream(url: string, fileType?: string): Promise<number> {
  const index = await requestCreateStreamInput()
  let chunkCount = 0
  try {
    const rawText = await urlToText(url)
    const text = stripBom(rawText)
    const parser = chooseParser(text, fileType)
    const numbers = parser === 'csv' ? parseCsvToNumbers(text) : parseNewlineDelimitedNumbers(text)
    for (const chunk of numbers) {
      sendStreamChunk(index, chunk)
      chunkCount += 1
    }
    if (chunkCount === 0) {
      console.warn(
        '[buildGetExternalStreams] No numeric data in file (empty file or no numbers parsed). Result may be [].',
      )
      useUIStore.getState().addToast(
        'The file has no numeric data. Use numbers (one per line) or CSV with numeric columns.',
        'error',
      )
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
    let skippedNoInputName = false
    let skippedNoFileUrl = false
    for (const edge of fileEdges) {
      const sourceNode = nodes.find((n) => n.id === edge.sourceId)
      const inputName = targetNode.inputs?.[edge.targetInputIndex]?.name
      if (!sourceNode || !inputName?.trim()) {
        skippedNoInputName = true
        continue
      }
      const url = sourceNode.url
      if (!url?.trim()) {
        skippedNoFileUrl = true
        continue
      }
      try {
        const index = await feedUrlToStream(url, sourceNode.fileType)
        result[inputName] = index
      } catch (e) {
        console.error('[buildGetExternalStreams] feed failed for', inputName, e)
        const msg = e instanceof Error ? e.message : String(e)
        if (msg.includes('File not available after reload')) {
          useUIStore.getState().addToast('File not available after reload. Re-drop the file to use it again.', 'error')
        }
        // Skip this input; LSP may see it as unbound
      }
    }
    if (fileEdges.length > 0 && Object.keys(result).length === 0) {
      console.warn(
        '[buildGetExternalStreams] File(s) wired but no stream bound. Ensure the computation has an input (e.g. "input x: Vector") and that the LSP has sent the node signature. Result may be [].',
      )
      if (skippedNoInputName && !skippedNoFileUrl) {
        useUIStore.getState().addToast(
          'Name the computation input (e.g. x) so the file can be connected.',
          'error',
        )
      } else if (skippedNoFileUrl && !skippedNoInputName) {
        useUIStore.getState().addToast(
          'Drop a file on the file block first, then wire it to the computation.',
          'error',
        )
      } else if (skippedNoInputName && skippedNoFileUrl) {
        useUIStore.getState().addToast(
          'Name the computation input (e.g. x) and drop a file on the file block, then wire them.',
          'error',
        )
      }
    }
    return result
  }
}
