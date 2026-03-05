/**
 * Unit tests for ComputationBoxNode.
 * Verifies that widget store subscription is isolated so result updates do not re-render the node (preserves editor focus).
 */

import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { join } from 'node:path'

const NODE_PATH = join(__dirname, 'computation-box-node.tsx')

describe('ComputationBoxNode', () => {
  it('renders three output handles: top, right, and bottom with distinct ids and testids', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    expect(source).toMatch(/COMPUTATION_OUTPUT_HANDLE_TOP/)
    expect(source).toMatch(/data-testid="computation-output-handle-top"/)
    expect(source).toMatch(/position=\{Position\.Top\}/)
    expect(source).toMatch(/COMPUTATION_OUTPUT_HANDLE_RIGHT/)
    expect(source).toMatch(/data-testid="computation-output-handle"/)
    expect(source).toMatch(/position=\{Position\.Right\}/)
    expect(source).toMatch(/COMPUTATION_OUTPUT_HANDLE_BOTTOM/)
    expect(source).toMatch(/data-testid="computation-output-handle-bottom"/)
    expect(source).toMatch(/position=\{Position\.Bottom\}/)
  })

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
    expect(source).toMatch(/ComputationResultBlock\s*\(\s*\{[\s\S]*?widgetId/)
  })

  it('ComputationResultBlock result area has minWidth 0 and overflow hidden so long errors do not expand node', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    const blockStart = source.indexOf('function ComputationResultBlock')
    const blockEnd = source.indexOf('function WidgetSubscription')
    expect(blockStart).toBeGreaterThanOrEqual(0)
    expect(blockEnd).toBeGreaterThan(blockStart)
    const blockSource = source.slice(blockStart, blockEnd)
    expect(blockSource).toMatch(/minWidth:\s*0/)
    expect(blockSource).toMatch(/overflow:\s*['"]hidden['"]/)
    expect(blockSource).toMatch(/data-testid="computation-result"/)
  })
})
