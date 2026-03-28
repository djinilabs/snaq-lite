/// <reference types="vite/client" />
import '../app.css'
import type { ReactNode } from 'react'
import { Link, Outlet, createRootRoute, HeadContent, Scripts } from '@tanstack/react-router'

function NotFoundComponent() {
  return (
    <div data-testid="not-found-page" style={{ padding: 24 }}>
      <p>Page not found.</p>
      <Link to="/">Home</Link>
    </div>
  )
}

export const Route = createRootRoute({
  notFoundComponent: NotFoundComponent,
  head: () => ({
    meta: [
      { charSet: 'utf-8' },
      { name: 'viewport', content: 'width=device-width, initial-scale=1' },
      { title: 'Snaq Lite' },
    ],
  }),
  component: RootComponent,
})

function RootComponent() {
  return (
    <RootDocument>
      <Outlet />
    </RootDocument>
  )
}

function RootDocument({ children }: Readonly<{ children: ReactNode }>) {
  return (
    <html lang="en">
      <head>
        <HeadContent />
      </head>
      <body>
        {children}
        <Scripts />
      </body>
    </html>
  )
}
