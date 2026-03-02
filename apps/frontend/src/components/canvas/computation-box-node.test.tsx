/**
 * Unit tests for ComputationBoxNode.
 * Verifies that widget store subscription is isolated so result updates do not re-render the node (preserves editor focus).
 */

import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { join } from 'node:path'

const NODE_PATH = join(__dirname, 'computation-box-node.tsx')

describe('ComputationBoxNode', () => {
  it('widget store subscription is in ComputationResultBlock so result updates do not re-render node (preserves editor focus)', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    // The main node must not subscribe to useWidgetStore((s) => s.byId[...]) so that when the result
    // updates (widgetDataUpdate → setWidget), only ComputationResultBlock re-renders and the editor keeps focus.
    const nodeComponentMatch = source.match(
      /export function ComputationBoxNode\s*\([^)]*\)\s*\{([\s\S]*?)^\s{2}return\s*\(/m,
    )
    expect(nodeComponentMatch).not.toBeNull()
    const nodeBody = nodeComponentMatch![1]
    expect(nodeBody).not.toMatch(/useWidgetStore\s*\(\s*\(\s*s\s*\)\s*=>\s*s\.byId/)
    // ComputationResultBlock should be the one that subscribes
    expect(source).toMatch(/function ComputationResultBlock/)
    expect(source).toMatch(/ComputationResultBlock.*widgetId/)
  })
})
