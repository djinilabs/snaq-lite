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

  it('setWidget appends elements when both current and incoming are Running with elements', () => {
    const a = { display: '1' }
    const b = { display: '2' }
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [a] },
    })
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [b] },
    })
    expect(useWidgetStore.getState().byId['w1']).toMatchObject({
      status: 'Running',
      payload: { elements: [a, b] },
    })
  })

  it('setWidget Completed replaces state entirely', () => {
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [{ display: '1' }] },
    })
    useWidgetStore.getState().setWidget('w1', {
      status: 'Completed',
      payload: { totalElements: 2 },
    })
    expect(useWidgetStore.getState().byId['w1']).toEqual({
      status: 'Completed',
      payload: { totalElements: 2 },
    })
  })

  it('setWidget Running with empty elements appends nothing', () => {
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [{ display: 'x' }] },
    })
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [] },
    })
    expect(useWidgetStore.getState().byId['w1']?.payload?.elements).toEqual([
      { display: 'x' },
    ])
  })

  it('setWidget Cancelled replaces state entirely', () => {
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [{ display: '1' }] },
    })
    useWidgetStore.getState().setWidget('w1', {
      status: 'Cancelled',
      payload: { reason: 'Unsubscribed' },
    })
    expect(useWidgetStore.getState().byId['w1']).toEqual({
      status: 'Cancelled',
      payload: { reason: 'Unsubscribed' },
    })
  })

  it('setWidget Error replaces state entirely', () => {
    useWidgetStore.getState().setWidget('w1', {
      status: 'Running',
      payload: { elements: [{ display: '1' }] },
    })
    useWidgetStore.getState().setWidget('w1', {
      status: 'Error',
      payload: { message: 'parse error' },
    })
    expect(useWidgetStore.getState().byId['w1']).toEqual({
      status: 'Error',
      payload: { message: 'parse error' },
    })
  })
})
