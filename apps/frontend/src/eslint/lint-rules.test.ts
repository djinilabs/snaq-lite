/**
 * Tests that ESLint and our lint rules run as expected.
 * Uses a minimal test config (test-eslint.config.js) to assert specific rules fire.
 */

import { describe, it, expect } from 'vitest'
import { join } from 'node:path'
import { ESLint } from 'eslint'

async function lintWithTestConfig(code: string, filename: string): Promise<ESLint.LintResult[]> {
  const eslint = new ESLint({
    overrideConfigFile: join(process.cwd(), 'src/eslint/test-eslint.config.js'),
  })
  return eslint.lintText(code, { filePath: filename })
}

describe('ESLint lint rules', () => {
  it('reports @typescript-eslint/no-unused-vars for unused variable', async () => {
    const results = await lintWithTestConfig('const x = 1;\n', 'fixture.ts')
    const messages = results.flatMap((r) => r.messages)
    const unused = messages.filter((m) => m.ruleId === '@typescript-eslint/no-unused-vars')
    expect(unused.length).toBeGreaterThanOrEqual(1)
    expect(unused[0].message).toMatch(/never used|assigned a value but never used/i)
  })

  it('does not report no-unused-vars for underscore-prefixed variable', async () => {
    const results = await lintWithTestConfig('const _ok = 1;\n', 'fixture.ts')
    const messages = results.flatMap((r) => r.messages)
    const unused = messages.filter((m) => m.ruleId === '@typescript-eslint/no-unused-vars')
    expect(unused).toHaveLength(0)
  })
})
