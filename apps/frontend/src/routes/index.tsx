import { createFileRoute } from '@tanstack/react-router'
import { GraphCanvas } from '~/components/canvas/graph-canvas'

export const Route = createFileRoute('/')({
  component: IndexPage,
})

function IndexPage() {
  return (
    <div style={{ width: '100vw', height: '100vh' }}>
      <GraphCanvas />
    </div>
  )
}
