/**
 * Dumb display: consumes streamed elements / display strings. Can be extended with Recharts/Chart.js.
 */

import type { WidgetState } from '~/store'

interface WidgetDataViewProps {
  state: WidgetState | undefined
}

export function WidgetDataView({ state }: WidgetDataViewProps) {
  if (!state) return <span style={{ color: '#666' }}>—</span>
  const { status, payload } = state
  if (status === 'Running' && payload?.elements?.length) {
    return (
      <div style={{ fontSize: 11, fontFamily: 'monospace' }}>
        {payload.elements.map((el, i) =>
          el === null ? (
            <span key={i}>?</span>
          ) : 'display' in el ? (
            <span key={i}>{el.display} </span>
          ) : (
            <span key={i} style={{ color: '#c66' }}>{el.message}</span>
          ),
        )}
      </div>
    )
  }
  if (status === 'Completed' && payload?.display) {
    return <span style={{ fontFamily: 'monospace' }}>{payload.display}</span>
  }
  if (status === 'Completed' && payload?.totalElements != null) {
    return <span>{payload.totalElements} elements</span>
  }
  if (status === 'Error' && payload?.message) {
    return <span style={{ color: '#c66' }}>{payload.message}</span>
  }
  if (status === 'Cancelled') {
    return <span style={{ color: '#888' }}>Cancelled</span>
  }
  return <span style={{ color: '#888' }}>{status}</span>
}
