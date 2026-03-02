import { describe, it, expect, beforeEach } from 'vitest'
import { useWidgetContentVersionStore } from './widget-content-version-store'

describe('widget-content-version-store', () => {
  beforeEach(() => {
    useWidgetContentVersionStore.setState({ byWidgetId: {} })
  })

  it('increment increases version for widget id', () => {
    useWidgetContentVersionStore.getState().increment('w1')
    expect(useWidgetContentVersionStore.getState().byWidgetId['w1']).toBe(1)
    useWidgetContentVersionStore.getState().increment('w1')
    expect(useWidgetContentVersionStore.getState().byWidgetId['w1']).toBe(2)
  })

  it('increment does not affect other widget ids', () => {
    useWidgetContentVersionStore.getState().increment('w1')
    useWidgetContentVersionStore.getState().increment('w2')
    expect(useWidgetContentVersionStore.getState().byWidgetId['w1']).toBe(1)
    expect(useWidgetContentVersionStore.getState().byWidgetId['w2']).toBe(1)
  })
})
