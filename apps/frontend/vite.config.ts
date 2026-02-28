/// <reference types="vitest/config" />
import { defineConfig } from 'vite'
import tsConfigPaths from 'vite-tsconfig-paths'
import { tanstackStart } from '@tanstack/react-start/plugin/vite'
import react from '@vitejs/plugin-react'

export default defineConfig(() => ({
  server: {
    port: 3000,
  },
  plugins: [
    tsConfigPaths(),
    ...(process.env.VITEST
      ? [react()]
      : [tanstackStart({ spa: { enabled: true } }), react()]),
  ],
  test: {
    environment: 'jsdom',
    globals: true,
    include: ['src/**/*.{test,spec}.{ts,tsx}'],
  },
}))
