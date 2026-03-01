import { describe, it, expect } from 'vitest'
import { getDragHandleSelector } from './graph-drag-handle'
import { getNodeDragHandleClassName } from './node-interaction-shell'
import {
  DRAG_HANDLE_CLASS_COMPUTATION,
  DRAG_HANDLE_CLASS_PRESENTATION,
} from '~/lib/constants'

describe('getDragHandleSelector', () => {
  it('returns computation drag handle selector for computation type', () => {
    expect(getDragHandleSelector('computation')).toBe(
      `.${DRAG_HANDLE_CLASS_COMPUTATION}`,
    )
  })

  it('returns presentation drag handle selector for presentation type', () => {
    expect(getDragHandleSelector('presentation')).toBe(
      `.${DRAG_HANDLE_CLASS_PRESENTATION}`,
    )
  })

  it('returns a valid CSS class selector starting with a dot', () => {
    expect(getDragHandleSelector('computation')).toMatch(/^\.[\w-]+$/)
    expect(getDragHandleSelector('presentation')).toMatch(/^\.[\w-]+$/)
  })

  it('matches getNodeDragHandleClassName result as class selector', () => {
    expect(getDragHandleSelector('computation')).toBe(
      `.${getNodeDragHandleClassName('computation')}`,
    )
    expect(getDragHandleSelector('presentation')).toBe(
      `.${getNodeDragHandleClassName('presentation')}`,
    )
  })
})
