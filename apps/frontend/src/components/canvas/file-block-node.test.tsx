/**
 * Unit tests for FileBlockNode.
 * Verifies structure and data-testids for file block (single output handle, kind file),
 * and fileBlockLabel edge cases.
 */

import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { fileBlockLabel } from './file-block-node'

const NODE_PATH = join(__dirname, 'file-block-node.tsx')

describe('fileBlockLabel', () => {
  it('returns "No file" when url is undefined', () => {
    expect(fileBlockLabel(undefined)).toBe('No file')
  })

  it('returns "No file" when url is empty string', () => {
    expect(fileBlockLabel('')).toBe('No file')
  })

  it('returns "File" for blob URLs', () => {
    expect(fileBlockLabel('blob:https://example.com/abc')).toBe('File')
  })

  it('returns last path segment for https URL with path', () => {
    expect(fileBlockLabel('https://example.com/data/numbers.csv')).toBe('numbers.csv')
  })

  it('returns "File" when path has no segment (root)', () => {
    expect(fileBlockLabel('https://example.com/')).toBe('File')
  })

  it('returns "File" for invalid URL (catch fallback)', () => {
    expect(fileBlockLabel('not-a-valid-url')).toBe('File')
  })
})

describe('FileBlockNode', () => {
  it('uses NodeFrame kind file and file-node testid', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    expect(source).toMatch(/kind="file"/)
    expect(source).toMatch(/nodeTestId="file-node"/)
    expect(source).toMatch(/titleTestId="file-drag-zone"/)
  })

  it('has single source handle with COMPUTATION_OUTPUT_HANDLE_RIGHT and file-output-handle testid', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    expect(source).toMatch(/COMPUTATION_OUTPUT_HANDLE_RIGHT/)
    expect(source).toMatch(/data-testid="file-output-handle"/)
    expect(source).toMatch(/type="source"/)
    expect(source).toMatch(/position=\{Position\.Right\}/)
  })

  it('has file-content zone and fileBlockLabel for No file / blob / URL', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    expect(source).toMatch(/data-testid="file-content"/)
    expect(source).toMatch(/fileBlockLabel/)
    expect(source).toMatch(/No file/)
    expect(source).toMatch(/Drop a file or add URL/)
  })
})
