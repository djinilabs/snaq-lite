/**
 * Pure helpers for project loading: UUID validation and snapshot → graph nodes.
 * Used by useProjectLoader; tested in isolation.
 */

import { nodeIdToUri } from '~/editor/virtual-uri'
import type { GraphNode } from '~/store'
import type { ProjectSnapshot } from '~/types/project'

const UUID_REGEX = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i

export function isValidUuid(s: string): boolean {
  return UUID_REGEX.test(s)
}

export function snapshotToGraphNodes(snapshot: ProjectSnapshot): GraphNode[] {
  return snapshot.nodes.map((n) => ({
    id: n.id,
    position: n.position,
    type: n.type,
    uri: nodeIdToUri(n.id),
    initialContent: n.type === 'computation' ? (n.content ?? '') : undefined,
    inputs: n.type === 'computation' && n.inputs?.length ? n.inputs : undefined,
  }))
}
