import { describe, it, expect, beforeEach } from 'vitest'
import { useUIStore } from './ui-store'

describe('ui-store', () => {
  beforeEach(() => {
    useUIStore.setState({ toasts: [] })
  })

  it('addToast appends toast with id and message', () => {
    useUIStore.getState().addToast('Hello')
    expect(useUIStore.getState().toasts).toHaveLength(1)
    expect(useUIStore.getState().toasts[0].message).toBe('Hello')
    expect(useUIStore.getState().toasts[0].id).toBeDefined()
    expect(useUIStore.getState().toasts[0].kind).toBe('info')
  })

  it('addToast with kind error', () => {
    useUIStore.getState().addToast('Failed', 'error')
    expect(useUIStore.getState().toasts[0].kind).toBe('error')
  })

  it('removeToast removes by id', () => {
    useUIStore.getState().addToast('A')
    const id = useUIStore.getState().toasts[0].id
    useUIStore.getState().addToast('B')
    useUIStore.getState().removeToast(id)
    expect(useUIStore.getState().toasts).toHaveLength(1)
    expect(useUIStore.getState().toasts[0].message).toBe('B')
  })
})
