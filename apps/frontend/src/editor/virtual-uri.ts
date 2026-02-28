/**
 * Virtual document URIs for graph nodes. Scheme snaq://graph/<id>.sl to match LSP and docs.
 */

import { VIRTUAL_URI_PREFIX } from '~/lib/constants'

const EXT = '.sl'

export function nodeIdToUri(nodeId: string): string {
  return `${VIRTUAL_URI_PREFIX}${nodeId}${EXT}`
}

export function uriToNodeId(uri: string): string | null {
  if (!uri.startsWith(VIRTUAL_URI_PREFIX) || !uri.endsWith(EXT)) return null
  return uri.slice(VIRTUAL_URI_PREFIX.length, -EXT.length) || null
}

export function isGraphNodeUri(uri: string): boolean {
  return uri.startsWith(VIRTUAL_URI_PREFIX)
}
