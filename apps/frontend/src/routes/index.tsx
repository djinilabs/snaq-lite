import { createFileRoute } from '@tanstack/react-router'

export const Route = createFileRoute('/')({
  component: HomePage,
})

function HomePage() {
  /* minHeight so the element has layout (empty main is 0×0 and reads as hidden in Playwright). */
  return <main data-testid="home-page" style={{ minHeight: '100vh' }} />
}
