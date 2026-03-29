import type { PublishNodeResultParams } from './types'
import type { CanvasNode } from './graph-patch'
import type { NodeSignatureUpdatedParams } from './types'

export type NodeSubscriptionEntry = {
  subscriptionId: string
  resultHandle?: string
}

export type NodeResultEntry = {
  status: string
  revision?: number
  payload?: Record<string, unknown>
}

export function resolveNodeUriFromPublish(
  params: PublishNodeResultParams,
  subscriptionUriById: Record<string, string>,
): string | undefined {
  if (typeof params.uri === 'string' && params.uri.length > 0) {
    return params.uri
  }
  if (!params.subscriptionId) {
    return undefined
  }
  return subscriptionUriById[params.subscriptionId]
}

export function upsertNodeSubscription(
  current: Record<string, NodeSubscriptionEntry>,
  uri: string,
  next: NodeSubscriptionEntry,
): Record<string, NodeSubscriptionEntry> {
  return {
    ...current,
    [uri]: next,
  }
}

export function applyPublishNodeResult(
  currentResults: Record<string, NodeResultEntry>,
  currentSubscriptions: Record<string, NodeSubscriptionEntry>,
  uri: string,
  params: PublishNodeResultParams,
): {
  nextResults: Record<string, NodeResultEntry>
  nextSubscriptions: Record<string, NodeSubscriptionEntry>
  resultHandle?: string
} {
  const nextResults: Record<string, NodeResultEntry> = {
    ...currentResults,
    [uri]: {
      status: params.status,
      revision: params.revision,
      payload: params.data,
    },
  }
  const nextSubscriptions = { ...currentSubscriptions }
  const maybeHandle = params.data?.resultHandle
  if (typeof maybeHandle === 'string') {
    nextSubscriptions[uri] = {
      ...(nextSubscriptions[uri] ?? { subscriptionId: params.subscriptionId }),
      resultHandle: maybeHandle,
    }
    return { nextResults, nextSubscriptions, resultHandle: maybeHandle }
  }
  return { nextResults, nextSubscriptions }
}

export function applyNodeSignatureUpdated(
  currentNodes: CanvasNode[],
  params: NodeSignatureUpdatedParams,
): CanvasNode[] {
  if (!params.uri) {
    return currentNodes
  }
  let changed = false
  const next = currentNodes.map((node) => {
    if (node.uri !== params.uri) {
      return node
    }
    changed = true
    return {
      ...node,
      params: params.inputs.map((input) => ({
        name: input.name,
        paramId: input.paramId,
        typeName: input.type,
      })),
    }
  })
  return changed ? next : currentNodes
}
