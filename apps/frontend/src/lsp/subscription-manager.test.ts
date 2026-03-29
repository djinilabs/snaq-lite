import { describe, expect, it } from 'vitest'
import {
  cursorKey,
  registerNodeSubscription,
  removeNodeSubscriptionByUri,
  resolveUriFromPublish,
  updateCursor,
  type SubscriptionState,
} from './subscription-manager'

describe('subscription manager', () => {
  it('registers subscriptions and keeps id/uri mapping in sync', () => {
    const empty: SubscriptionState = { byUri: {}, uriById: {} }
    const first = registerNodeSubscription(empty, 'snaq://canvas-a/node-1.sl', {
      subscriptionId: 'sub-1',
      resultHandle: 'h-1',
    })
    const replaced = registerNodeSubscription(first, 'snaq://canvas-a/node-1.sl', {
      subscriptionId: 'sub-2',
      resultHandle: 'h-2',
    })
    expect(first.uriById['sub-1']).toBe('snaq://canvas-a/node-1.sl')
    expect(replaced.uriById['sub-1']).toBeUndefined()
    expect(replaced.uriById['sub-2']).toBe('snaq://canvas-a/node-1.sl')
  })

  it('removes subscriptions by uri', () => {
    const current: SubscriptionState = {
      byUri: {
        'snaq://canvas-a/node-1.sl': { subscriptionId: 'sub-1' },
      },
      uriById: { 'sub-1': 'snaq://canvas-a/node-1.sl' },
    }
    const next = removeNodeSubscriptionByUri(current, 'snaq://canvas-a/node-1.sl')
    expect(next.byUri['snaq://canvas-a/node-1.sl']).toBeUndefined()
    expect(next.uriById['sub-1']).toBeUndefined()
  })

  it('resolves uri from publish payload or fallback map', () => {
    expect(resolveUriFromPublish('sub-1', { 'sub-1': 'a' }, 'b')).toBe('b')
    expect(resolveUriFromPublish('sub-1', { 'sub-1': 'a' })).toBe('a')
  })

  it('stores cursor per handle/path key', () => {
    const key = cursorKey('h-1', ['rows', 0])
    expect(key).toContain('h-1')
    const next = updateCursor({}, 'h-1', { offset: 4, cursor: 'c-1' }, ['rows', 0])
    expect(next[key]).toEqual({ offset: 4, cursor: 'c-1' })
  })
})

