/**
 * Unit tests for ResultDetailModal: visibility, close button, Escape key.
 */

import { describe, it, expect, beforeEach, vi } from 'vitest'
import { act } from 'react'
import { createRoot } from 'react-dom/client'
import { ResultDetailModal } from './result-detail-modal'
import { useUIStore } from '~/store/ui-store'
import { useWidgetStore } from '~/store/widget-store'

vi.mock('~/lsp/fetch-result-slice', () => ({
  fetchResultSlice: vi.fn().mockResolvedValue({
    elements: [{ display: '1' }, { display: '2' }],
    totalCount: 2,
    hasMore: false,
  }),
}))

async function renderModal(): Promise<{ container: HTMLElement; unmount: () => void }> {
  const container = document.createElement('div')
  document.body.appendChild(container)
  const root = createRoot(container)
  root.render(<ResultDetailModal />)
  await act(async () => {})
  return {
    container,
    unmount: () => {
      root.unmount()
      document.body.removeChild(container)
    },
  }
}

describe('ResultDetailModal', () => {
  beforeEach(() => {
    useUIStore.setState({ resultDetailWidgetId: null })
    useWidgetStore.setState({ byId: {} })
  })

  it('renders nothing when resultDetailWidgetId is null', async () => {
    const { unmount } = await renderModal()
    const modal = document.body.querySelector('[data-testid="result-detail-modal"]')
    expect(modal).toBeNull()
    unmount()
  })

  it('renders dialog when resultDetailWidgetId is set and widget has Completed Vector payload', async () => {
    await act(async () => {
      useUIStore.setState({ resultDetailWidgetId: 'w1' })
      useWidgetStore.setState({
        byId: {
          w1: {
            status: 'Completed',
            payload: {
              resultType: 'Vector',
              resultSummary: { length: 2 },
              totalElements: 2,
            },
          },
        },
      })
    })
    const { unmount } = await renderModal()
    const modal = document.body.querySelector('[data-testid="result-detail-modal"]')
    expect(modal).not.toBeNull()
    expect(modal?.getAttribute('aria-modal')).toBe('true')
    unmount()
  })

  it('close button calls setResultDetailWidgetId(null)', async () => {
    useUIStore.setState({ resultDetailWidgetId: 'w2' })
    useWidgetStore.setState({
      byId: {
        w2: {
          status: 'Completed',
          payload: {
            resultType: 'Vector',
            resultSummary: { length: 1 },
            totalElements: 1,
          },
        },
      },
    })
    const { unmount } = await renderModal()
    const closeBtn = document.body.querySelector('[data-testid="result-detail-close-btn"]')
    expect(closeBtn).not.toBeNull()
    await act(async () => {
      ;(closeBtn as HTMLButtonElement).click()
    })
    expect(useUIStore.getState().resultDetailWidgetId).toBeNull()
    unmount()
  })

  it('Escape key closes the modal', async () => {
    useUIStore.setState({ resultDetailWidgetId: 'w3' })
    useWidgetStore.setState({
      byId: {
        w3: {
          status: 'Completed',
          payload: {
            resultType: 'Vector',
            resultSummary: { length: 1 },
            totalElements: 1,
          },
        },
      },
    })
    const { unmount } = await renderModal()
    expect(useUIStore.getState().resultDetailWidgetId).toBe('w3')
    await act(async () => {
      document.dispatchEvent(new KeyboardEvent('keydown', { key: 'Escape', bubbles: true }))
    })
    expect(useUIStore.getState().resultDetailWidgetId).toBeNull()
    unmount()
  })

  it('shows scalar display when resultType is Scalar', async () => {
    useUIStore.setState({ resultDetailWidgetId: 'w4' })
    useWidgetStore.setState({
      byId: {
        w4: {
          status: 'Completed',
          payload: { resultType: 'Scalar', display: '42' },
        },
      },
    })
    const { unmount } = await renderModal()
    const modal = document.body.querySelector('[data-testid="result-detail-modal"]')
    expect(modal).not.toBeNull()
    expect(modal?.textContent).toContain('42')
    unmount()
  })

  it('shows error message when status is Error', async () => {
    useUIStore.setState({ resultDetailWidgetId: 'w5' })
    useWidgetStore.setState({
      byId: {
        w5: {
          status: 'Error',
          payload: { message: 'Run failed: division by zero' },
        },
      },
    })
    const { unmount } = await renderModal()
    const modal = document.body.querySelector('[data-testid="result-detail-modal"]')
    expect(modal).not.toBeNull()
    expect(modal?.textContent).toContain('Run failed: division by zero')
    unmount()
  })

  it('shows Result was cancelled when status is Cancelled', async () => {
    useUIStore.setState({ resultDetailWidgetId: 'w6' })
    useWidgetStore.setState({
      byId: {
        w6: { status: 'Cancelled' },
      },
    })
    const { unmount } = await renderModal()
    const modal = document.body.querySelector('[data-testid="result-detail-modal"]')
    expect(modal).not.toBeNull()
    expect(modal?.textContent).toContain('Result was cancelled')
    unmount()
  })
})
