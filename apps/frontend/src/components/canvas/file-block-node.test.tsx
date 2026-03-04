/**
 * Unit tests for FileBlockNode.
 * Verifies structure and data-testids for file block (single output handle, kind file),
 * and fileBlockLabel edge cases.
 */

import { describe, it, expect } from 'vitest'
import { readFileSync } from 'node:fs'
import { join } from 'node:path'
import { fileBlockLabel, fileBlockTypeLabel } from './file-block-node'

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

describe('fileBlockTypeLabel', () => {
  it('returns "—" when no fileType and no url', () => {
    expect(fileBlockTypeLabel(undefined, undefined)).toBe('—')
  })

  it('returns friendly label for common MIME types', () => {
    expect(fileBlockTypeLabel('text/csv', undefined)).toBe('CSV')
    expect(fileBlockTypeLabel('text/plain', undefined)).toBe('Plain text')
    expect(fileBlockTypeLabel('application/json', undefined)).toBe('JSON')
  })

  it('returns MIME type when not a known shorthand', () => {
    expect(fileBlockTypeLabel('application/octet-stream', undefined)).toBe('application/octet-stream')
  })

  it('derives from URL when fileType is missing', () => {
    expect(fileBlockTypeLabel(undefined, 'blob:https://example.com/x')).toBe('Local file')
    expect(fileBlockTypeLabel(undefined, 'data:text/plain,hello')).toBe('Data URL')
    expect(fileBlockTypeLabel(undefined, 'https://example.com/d.csv')).toBe('CSV')
    expect(fileBlockTypeLabel(undefined, 'https://example.com/d.json')).toBe('JSON')
    expect(fileBlockTypeLabel(undefined, 'https://example.com/notes.txt')).toBe('Plain text')
  })

  it('prefers fileType over URL-derived label', () => {
    expect(fileBlockTypeLabel('text/csv', 'blob:xxx')).toBe('CSV')
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

  it('has file-content zone, file-type and file-url testids, and fileBlockLabel for No file / blob / URL', () => {
    const source = readFileSync(NODE_PATH, 'utf-8')
    expect(source).toMatch(/data-testid="file-content"/)
    expect(source).toMatch(/data-testid="file-type"/)
    expect(source).toMatch(/data-testid="file-url"/)
    expect(source).toMatch(/fileBlockLabel/)
    expect(source).toMatch(/No file/)
    expect(source).toMatch(/Drop a file or add URL/)
  })
})
