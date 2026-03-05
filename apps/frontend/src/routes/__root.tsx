/// <reference types="vite/client" />
import '../app.css'
import '@xyflow/react/dist/style.css'
import { useEffect } from 'react'
import type { ReactNode } from 'react'
import {
  Link,
  Outlet,
  createRootRoute,
  HeadContent,
  Scripts,
} from '@tanstack/react-router'
import { LspProvider } from '~/components/lsp-provider'
import { ToastList } from '~/components/toast-list'
import { ResultDetailModal } from '~/components/presentation/result-detail-modal'
import { useProjectsIndexStore } from '~/store'

function NotFoundComponent() {
  return (
    <div
      data-testid="not-found-page"
      style={{
        minHeight: '100vh',
        background: 'var(--bg-primary)',
        color: 'var(--text-primary)',
        padding: 32,
        maxWidth: 640,
        margin: '0 auto',
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'flex-start',
        justifyContent: 'center',
      }}
    >
      <h1 style={{ margin: '0 0 8px', fontSize: 28, fontWeight: 600 }}>Page not found</h1>
      <p style={{ margin: '0 0 24px', color: 'var(--text-secondary)', fontSize: 15 }}>
        The page you&apos;re looking for doesn&apos;t exist or has been moved.
      </p>
      <Link
        to="/"
        style={{
          padding: '10px 20px',
          background: 'var(--accent)',
          color: '#fff',
          border: 'none',
          borderRadius: 'var(--radius-sm)',
          fontWeight: 500,
          textDecoration: 'none',
        }}
      >
        Back to projects
      </Link>
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
    links: [
      {
        rel: 'preconnect',
        href: 'https://fonts.googleapis.com',
      },
      {
        rel: 'preconnect',
        href: 'https://fonts.gstatic.com',
        crossOrigin: 'anonymous',
      },
      {
        rel: 'stylesheet',
        href: 'https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600&family=JetBrains+Mono:wght@400;500&display=swap',
      },
    ],
  }),
  component: RootComponent,
})

function RootComponent() {
  const hydrate = useProjectsIndexStore((s) => s.hydrate)
  useEffect(() => {
    hydrate()
  }, [hydrate])
  return (
    <RootDocument>
      <LspProvider>
        <Outlet />
        <ToastList />
        <ResultDetailModal />
      </LspProvider>
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
