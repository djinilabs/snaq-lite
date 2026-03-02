import '~/monaco-environment'
import { StartClient } from '@tanstack/react-start/client'
import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'

const rootEl = document.getElementById('root')
if (rootEl) {
  createRoot(rootEl).render(
    <StrictMode>
      <StartClient />
    </StrictMode>,
  )
}
