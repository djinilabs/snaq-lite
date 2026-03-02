import { describe, it, expect } from 'vitest'
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

  it('renders dash when state is undefined', async () => {
    const { container, unmount } = await render(<WidgetDataView state={undefined} />)
    const span = container.querySelector('span')
    expect(span).not.toBeNull()
    expect(span!.textContent).toBe('\u2014') // em dash as in widget-data-view
    unmount()
  })
})
