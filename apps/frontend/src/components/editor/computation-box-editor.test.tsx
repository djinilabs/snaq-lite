/**
 * Unit tests for ComputationBoxEditor.
 * Verifies that the editor effect does not depend on initialContent so that
 * parent re-renders (e.g. when result/widget updates) do not recreate the editor and lose focus.
 */

import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { join } from 'node:path'

const EDITOR_PATH = join(
  __dirname,
  'computation-box-editor.tsx',
)

describe('ComputationBoxEditor', () => {
  it('editor effect does not list initialContent in dependency array (avoids focus loss when result updates)', () => {
    const source = readFileSync(EDITOR_PATH, 'utf-8')
    // The effect that creates/disposes the Monaco editor must not depend on initialContent,
    // so that parent re-renders (e.g. after widget/result update) do not recreate the editor.
    // Find the useEffect that contains getOrCreateModel and editor.create, then its dependency array.
    const effectMatch = source.match(
      /useEffect\s*\(\s*\(\)\s*=>\s*\{[\s\S]*?getOrCreateModel[\s\S]*?\},\s*\[([^\]]+)\]\s*\)/,
    )
    expect(effectMatch).not.toBeNull()
    const deps = effectMatch![1]
    expect(deps).not.toMatch(/\binitialContent\b/)
    expect(deps).toMatch(/\bnodeId\b/)
    expect(deps).toMatch(/\buri\b/)
    expect(deps).toMatch(/\bvisible\b/)
  })
})
