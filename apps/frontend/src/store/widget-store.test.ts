import { describe, it, expect, beforeEach } from 'vitest'
import { useWidgetStore } from './widget-store'

describe('widget-store', () => {
  beforeEach(() => {
    useWidgetStore.setState({ byId: {} })
  })

  it('setWidget stores state by widgetId', () => {
    useWidgetStore.getState().setWidget('w1', { status: 'Running' })
    expect(useWidgetStore.getState().byId['w1']).toEqual({ status: 'Running' })
  })

  it('setWidget with payload', () => {
    useWidgetStore.getState().setWidget('w2', {
      status: 'Completed',
      payload: { totalElements: 5 },
    })
    expect(useWidgetStore.getState().byId['w2']).toMatchObject({
      status: 'Completed',
      payload: { totalElements: 5 },
    })
  })

  it('removeWidget deletes by id', () => {
    useWidgetStore.getState().setWidget('w1', { status: 'Running' })
    useWidgetStore.getState().removeWidget('w1')
    expect(useWidgetStore.getState().byId['w1']).toBeUndefined()
  })
})
