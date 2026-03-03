import { describe, it, expect } from 'vitest'
import { buildComputationDocumentContent } from './computation-document-content'

describe('buildComputationDocumentContent', () => {
  it('returns body only when no inputs', () => {
    expect(buildComputationDocumentContent('x * 10', undefined)).toBe('x * 10')
    expect(buildComputationDocumentContent('x * 10', [])).toBe('x * 10')
  })

  it('prepends input decls when body does not start with "input "', () => {
    expect(
      buildComputationDocumentContent('fff * 333', [
        { name: 'fff', type: 'Numeric' },
      ]),
    ).toBe('input fff: Numeric\nfff * 333')
  })

  it('returns body as-is when body already starts with "input "', () => {
    const body = 'input abc: Numeric\nabc * 10'
    expect(
      buildComputationDocumentContent(body, [{ name: 'abc', type: 'Numeric' }]),
    ).toBe(body)
  })

  it('filters out inputs with empty name', () => {
    expect(
      buildComputationDocumentContent('x', [
        { name: '', type: 'Numeric' },
        { name: 'x', type: 'Vector' },
      ]),
    ).toBe('input x: Vector\nx')
  })
})
