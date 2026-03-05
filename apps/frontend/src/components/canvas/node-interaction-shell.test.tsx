import { describe, it, expect } from 'vitest'
import { renderToStaticMarkup } from 'react-dom/server'
import {
  DRAG_HANDLE_CLASS_COMPUTATION,
  DRAG_HANDLE_CLASS_PRESENTATION,
  NODRAG_CLASS,
  NOWHEEL_CLASS,
} from '~/lib/constants'
import {
  getNodeDragHandleClassName,
  NodeContentZone,
  NodeFrame,
} from './node-interaction-shell'

describe('node interaction shell', () => {
  describe('getNodeDragHandleClassName', () => {
    it('returns drag handle class name per node kind', () => {
      expect(getNodeDragHandleClassName('computation')).toBe(
        DRAG_HANDLE_CLASS_COMPUTATION,
      )
      expect(getNodeDragHandleClassName('presentation')).toBe(
        DRAG_HANDLE_CLASS_PRESENTATION,
      )
    })
  })

  describe('NodeFrame', () => {
    it('renders with nopan root and computation drag zone class', () => {
      const html = renderToStaticMarkup(
        <NodeFrame kind="computation" title="Computation" nodeTestId="node">
          <div>content</div>
        </NodeFrame>,
      )
      expect(html).toContain('class="nopan"')
      expect(html).toContain(`class="${DRAG_HANDLE_CLASS_COMPUTATION}"`)
      expect(html).toContain('data-testid="node"')
    })

    it('renders presentation kind with presentation drag zone class', () => {
      const html = renderToStaticMarkup(
        <NodeFrame kind="presentation" title="Presentation" nodeTestId="pres">
          <span>body</span>
        </NodeFrame>,
      )
      expect(html).toContain(`class="${DRAG_HANDLE_CLASS_PRESENTATION}"`)
      expect(html).toContain('>Presentation<')
    })

    it('renders titleTestId on the drag zone element', () => {
      const html = renderToStaticMarkup(
        <NodeFrame
          kind="computation"
          title="Computation"
          titleTestId="computation-drag-zone"
        >
          <div>content</div>
        </NodeFrame>,
      )
      expect(html).toContain('data-testid="computation-drag-zone"')
    })

    it('applies minHeight when provided', () => {
      const html = renderToStaticMarkup(
        <NodeFrame kind="computation" title="Computation" minHeight={200}>
          <div>content</div>
        </NodeFrame>,
      )
      expect(html).toMatch(/min-height:\s*200px/)
    })

    it('applies outline style when selected', () => {
      const html = renderToStaticMarkup(
        <NodeFrame kind="computation" title="Computation" selected>
          <div>content</div>
        </NodeFrame>,
      )
      expect(html).toContain('outline')
      expect(html).toContain('var(--accent)')
    })

    it('uses flex column layout so result area can shrink and long errors do not expand node', () => {
      const html = renderToStaticMarkup(
        <NodeFrame kind="computation" title="Computation" nodeTestId="node">
          <div>content</div>
        </NodeFrame>,
      )
      expect(html).toMatch(/display:\s*flex/)
      expect(html).toMatch(/flex-direction:\s*column/)
    })
  })

  describe('NodeContentZone', () => {
    it('renders with nodrag and optional nowheel and custom className', () => {
      const html = renderToStaticMarkup(
        <NodeContentZone nowheel className="custom-zone">
          inner
        </NodeContentZone>,
      )
      expect(html).toContain(NODRAG_CLASS)
      expect(html).toContain(NOWHEEL_CLASS)
      expect(html).toContain('custom-zone')
    })

    it('renders with only nodrag when nowheel is false', () => {
      const html = renderToStaticMarkup(
        <NodeContentZone>content</NodeContentZone>,
      )
      expect(html).toContain(NODRAG_CLASS)
      expect(html).not.toContain(NOWHEEL_CLASS)
    })

    it('forwards data-testid and style to the div', () => {
      const html = renderToStaticMarkup(
        <NodeContentZone
          data-testid="computation-editor-zone"
          style={{ cursor: 'text' }}
        >
          editor
        </NodeContentZone>,
      )
      expect(html).toContain('data-testid="computation-editor-zone"')
      expect(html).toContain('cursor:text')
    })
  })
})
