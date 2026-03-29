import type { PageCursor } from './pagination'

export type NodeSubscriptionEntry = {
  subscriptionId: string
  resultHandle?: string
}

export type SubscriptionState = {
  byUri: Record<string, NodeSubscriptionEntry>
  uriById: Record<string, string>
}

export function registerNodeSubscription(
  current: SubscriptionState,
  uri: string,
  entry: NodeSubscriptionEntry,
): SubscriptionState {
  const previous = current.byUri[uri]
  const nextByUri = {
    ...current.byUri,
    [uri]: entry,
  }
  const nextUriById = { ...current.uriById }
  if (previous) {
    delete nextUriById[previous.subscriptionId]
  }
  nextUriById[entry.subscriptionId] = uri
  return {
    byUri: nextByUri,
    uriById: nextUriById,
  }
}

export function removeNodeSubscriptionByUri(current: SubscriptionState, uri: string): SubscriptionState {
  const previous = current.byUri[uri]
  if (!previous) {
    return current
  }
  const nextByUri = { ...current.byUri }
  delete nextByUri[uri]
  const nextUriById = { ...current.uriById }
  delete nextUriById[previous.subscriptionId]
  return {
    byUri: nextByUri,
    uriById: nextUriById,
  }
}

export function resolveUriFromPublish(
  subscriptionId: string,
  uriById: Record<string, string>,
  notificationUri?: string,
): string | undefined {
  if (notificationUri) {
    return notificationUri
  }
  return uriById[subscriptionId]
}

export function cursorKey(resultHandle: string, path: Array<string | number> = []): string {
  return `${resultHandle}:${JSON.stringify(path)}`
}

export function updateCursor(
  current: Record<string, PageCursor>,
  resultHandle: string,
  cursor: PageCursor,
  path: Array<string | number> = [],
): Record<string, PageCursor> {
  return {
    ...current,
    [cursorKey(resultHandle, path)]: cursor,
  }
}

