import { describe, it, expect, vi } from 'vitest'
import { act } from 'react'
import { createRoot } from 'react-dom/client'
import { WidgetDataView } from './widget-data-view'

async function render(
  ui: React.ReactElement,
): Promise<{ container: HTMLElement; unmount: () => void }> {
  const container = document.createElement('div')
  document.body.appendChild(container)
  const root = createRoot(container)
  root.render(ui)
  await act(async () => {})
  return {
    container,
    unmount: () => {
      root.unmount()
      document.body.removeChild(container)
    },
  }
}

describe('WidgetDataView', () => {
  it('renders payload.display when status is Completed', async () => {
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: { display: '42' },
        }}
      />,
    )
    expect(container.textContent).toBe('42')
    unmount()
  })

  it('renders "undefined" when resultType is Undefined (with or without display)', async () => {
    const { container: c1, unmount: u1 } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: { resultType: 'Undefined', display: 'undefined' },
        }}
      />,
    )
    expect(c1.textContent).toContain('undefined')
    u1()
    const { container: c2, unmount: u2 } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: { resultType: 'Undefined' },
        }}
      />,
    )
    expect(c2.textContent).toContain('undefined')
    u2()
  })

  it('renders dash when state is undefined', async () => {
    const { container, unmount } = await render(<WidgetDataView state={undefined} />)
    const span = container.querySelector('span')
    expect(span).not.toBeNull()
    expect(span!.textContent).toBe('\u2014') // em dash as in widget-data-view
    unmount()
  })

  it('renders error message when status is Error and applies wrap styles so long errors do not expand block', async () => {
    const longMessage = 'Dimension mismatch: expected length 2 but got 3 in vector operation at line 1'
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Error',
          payload: { message: longMessage },
        }}
      />,
    )
    expect(container.textContent).toContain(longMessage)
    const span = container.querySelector('span')
    expect(span).not.toBeNull()
    const style = span!.getAttribute('style') ?? ''
    expect(style).toMatch(/word-break|overflow-wrap/)
    unmount()
  })

  it('renders Completed display with wrap style so long output does not expand block', async () => {
    const longDisplay = '1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 = 55 (symbolic)'
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: { display: longDisplay },
        }}
      />,
    )
    expect(container.textContent).toBe(longDisplay)
    const span = container.querySelector('span')
    expect(span?.getAttribute('style')).toMatch(/word-break|overflow-wrap/)
    unmount()
  })

  it('renders error output with role="alert" and Copy button for full message', async () => {
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Error',
          payload: { message: 'Something went wrong' },
        }}
      />,
    )
    const alert = container.querySelector('[role="alert"]')
    expect(alert).not.toBeNull()
    expect(alert!.textContent).toContain('Something went wrong')
    const copyBtn = container.querySelector('button[title="Copy full message"]')
    expect(copyBtn).not.toBeNull()
    unmount()
  })

  it('renders Vector summary and View details button when resultType is Vector and onViewDetails provided', async () => {
    const onViewDetails = vi.fn()
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: {
            resultType: 'Vector',
            resultSummary: { length: 10 },
            totalElements: 10,
          },
        }}
        widgetId="w1"
        onViewDetails={onViewDetails}
      />,
    )
    expect(container.textContent).toContain('Vector (10 elements)')
    const btn = container.querySelector('[data-testid="view-details-btn"]')
    expect(btn).not.toBeNull()
    await act(async () => {
      ;(btn as HTMLButtonElement).click()
    })
    expect(onViewDetails).toHaveBeenCalledWith('w1')
    unmount()
  })

  it('renders Vector summary without View details button when onViewDetails is not provided', async () => {
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: {
            resultType: 'Vector',
            resultSummary: { length: 5 },
            totalElements: 5,
          },
        }}
        widgetId="w1"
      />,
    )
    expect(container.textContent).toContain('Vector (5 elements)')
    const btn = container.querySelector('[data-testid="view-details-btn"]')
    expect(btn).toBeNull()
    unmount()
  })

  it('renders Map summary and View details button when resultType is Map and onViewDetails provided', async () => {
    const onViewDetails = vi.fn()
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Completed',
          payload: {
            resultType: 'Map',
            resultSummary: { keyCount: 5 },
            totalElements: 5,
          },
        }}
        widgetId="w2"
        onViewDetails={onViewDetails}
      />,
    )
    expect(container.textContent).toContain('Map (5 keys)')
    const btn = container.querySelector('[data-testid="view-details-btn"]')
    expect(btn).not.toBeNull()
    await act(async () => {
      ;(btn as HTMLButtonElement).click()
    })
    expect(onViewDetails).toHaveBeenCalledWith('w2')
    unmount()
  })

  it('renders error element in Running state with wrap styles and minWidth 0 on container', async () => {
    const { container, unmount } = await render(
      <WidgetDataView
        state={{
          status: 'Running',
          payload: {
            elements: [{ kind: 'error', message: 'Stream input not available' }],
          },
        }}
      />,
    )
    expect(container.textContent).toContain('Stream input not available')
    const wrapperDiv = container.querySelector('div')
    expect(wrapperDiv).not.toBeNull()
    const wrapperStyle = wrapperDiv!.getAttribute('style') ?? ''
    expect(wrapperStyle).toMatch(/min-width:\s*0/)
    const spans = container.querySelectorAll('span')
    const withWrap = Array.from(spans).find(
      (s) =>
        (s.getAttribute('style') ?? '').includes('break-word') ||
        (s.getAttribute('style') ?? '').includes('break-all'),
    )
    expect(withWrap).not.toBeUndefined()
    expect(withWrap!.textContent).toContain('Stream input not available')
    const alert = container.querySelector('[role="alert"]')
    expect(alert).not.toBeNull()
    expect(alert!.textContent).toContain('Stream input not available')
    const copyBtn = container.querySelector('button[title="Copy full message"]')
    expect(copyBtn).not.toBeNull()
    unmount()
  })
})
