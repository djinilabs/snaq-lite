import { describe, it, expect, vi } from 'vitest'
import type { ReactElement } from 'react'
import { act } from 'react'
import { createRoot } from 'react-dom/client'
import { AutoSaveContext, useAutoSave } from './auto-save-context'

function Consumer() {
  const autoSave = useAutoSave()
  if (autoSave === null) return <span data-testid="auto-save">null</span>
  return (
    <span data-testid="auto-save">
      <button type="button" onClick={autoSave.requestSave} data-testid="request-save-btn">
        save
      </button>
    </span>
  )
}

function render(ui: ReactElement): { container: HTMLElement; unmount: () => void } {
  const container = document.createElement('div')
  document.body.appendChild(container)
  const root = createRoot(container)
  act(() => {
    root.render(ui)
  })
  return {
    container,
    unmount: () => {
      root.unmount()
      document.body.removeChild(container)
    },
  }
}

describe('auto-save-context', () => {
  it('useAutoSave returns null when outside provider', () => {
    const { container, unmount } = render(<Consumer />)
    const el = container.querySelector('[data-testid="auto-save"]')
    expect(el).not.toBeNull()
    expect(el?.textContent).toBe('null')
    unmount()
  })

  it('useAutoSave returns context value when inside provider', () => {
    const requestSave = vi.fn()
    const { container, unmount } = render(
      <AutoSaveContext.Provider value={{ requestSave }}>
        <Consumer />
      </AutoSaveContext.Provider>,
    )
    const btn = container.querySelector('[data-testid="request-save-btn"]') as HTMLButtonElement
    expect(btn).not.toBeNull()
    btn?.click()
    expect(requestSave).toHaveBeenCalledTimes(1)
    unmount()
  })

  it('calling requestSave when from context does not throw', () => {
    const requestSave = vi.fn()
    const { container, unmount } = render(
      <AutoSaveContext.Provider value={{ requestSave }}>
        <Consumer />
      </AutoSaveContext.Provider>,
    )
    const btn = container.querySelector('[data-testid="request-save-btn"]') as HTMLButtonElement
    expect(() => btn?.click()).not.toThrow()
    unmount()
  })
})
