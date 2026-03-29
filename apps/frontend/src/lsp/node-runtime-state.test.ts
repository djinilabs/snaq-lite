import { describe, expect, it } from 'vitest'
import {
  applyNodeSignatureUpdated,
  applyPublishNodeResult,
  resolveNodeUriFromPublish,
  upsertNodeSubscription,
  type NodeSubscriptionEntry,
} from './node-runtime-state'
import type { PublishNodeResultParams } from './types'

describe('node runtime state helpers', () => {
  it('resolves node URI from payload URI or subscription map', () => {
    const subMap = { 'sub-1': 'snaq://canvas-a/node-2.sl' }
    const withUri: PublishNodeResultParams = {
      subscriptionId: 'sub-1',
      status: 'Completed',
      uri: 'snaq://canvas-a/node-2.sl',
    }
    const fromMap: PublishNodeResultParams = {
      subscriptionId: 'sub-1',
      status: 'Completed',
    }
    expect(resolveNodeUriFromPublish(withUri, subMap)).toBe('snaq://canvas-a/node-2.sl')
    expect(resolveNodeUriFromPublish(fromMap, subMap)).toBe('snaq://canvas-a/node-2.sl')
  })

  it('upserts per-node subscriptions without clobbering siblings', () => {
    const current: Record<string, NodeSubscriptionEntry> = {
      'snaq://canvas-a/node-1.sl': { subscriptionId: 'sub-a', resultHandle: 'h-a' },
    }
    const next = upsertNodeSubscription(current, 'snaq://canvas-a/node-2.sl', {
      subscriptionId: 'sub-b',
      resultHandle: 'h-b',
    })
    expect(next['snaq://canvas-a/node-1.sl']).toEqual({ subscriptionId: 'sub-a', resultHandle: 'h-a' })
    expect(next['snaq://canvas-a/node-2.sl']).toEqual({ subscriptionId: 'sub-b', resultHandle: 'h-b' })
  })

  it('applies publish updates and captures resultHandle for target node only', () => {
    const result = applyPublishNodeResult(
      { 'snaq://canvas-a/node-1.sl': { status: 'Completed' } },
      { 'snaq://canvas-a/node-1.sl': { subscriptionId: 'sub-a' } },
      'snaq://canvas-a/node-1.sl',
      {
        subscriptionId: 'sub-a',
        status: 'Running',
        revision: 2,
        data: { resultHandle: 'h-2' },
      },
    )
    expect(result.nextResults['snaq://canvas-a/node-1.sl']).toEqual({
      status: 'Running',
      revision: 2,
      payload: { resultHandle: 'h-2' },
    })
    expect(result.nextSubscriptions['snaq://canvas-a/node-1.sl']).toEqual({
      subscriptionId: 'sub-a',
      resultHandle: 'h-2',
    })
    expect(result.resultHandle).toBe('h-2')
  })

  it('reconciles node params from nodeSignatureUpdated as canonical source', () => {
    const currentNodes = [
      {
        uri: 'snaq://canvas-a/node-1.sl',
        source: '1 + 2',
        params: [],
      },
      {
        uri: 'snaq://canvas-a/node-2.sl',
        source: '$x',
        params: [{ name: 'x_old', paramId: 'p1', typeName: 'Undefined' }],
      },
    ]
    const next = applyNodeSignatureUpdated(currentNodes, {
      uri: 'snaq://canvas-a/node-2.sl',
      inputs: [
        { name: 'x', paramId: 'p1', type: 'Vector' },
        { name: 'y', paramId: 'p2', type: 'Numeric' },
      ],
      outputType: 'Vector',
    })
    expect(next[0].params).toEqual([])
    expect(next[1].params).toEqual([
      { name: 'x', paramId: 'p1', typeName: 'Vector' },
      { name: 'y', paramId: 'p2', typeName: 'Numeric' },
    ])
  })

  it('prefers payload uri over stale subscription map after canvas switch', () => {
    const staleMap = { 'sub-1': 'snaq://canvas-a/node-2.sl' }
    const publish: PublishNodeResultParams = {
      subscriptionId: 'sub-1',
      status: 'Completed',
      uri: 'snaq://canvas-b/node-2.sl',
    }
    expect(resolveNodeUriFromPublish(publish, staleMap)).toBe('snaq://canvas-b/node-2.sl')
  })
})
