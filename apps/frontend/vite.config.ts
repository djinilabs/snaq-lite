/// <reference types="vitest/config" />
import path from 'node:path'
import { fileURLToPath } from 'node:url'
import { defineConfig } from 'vite'
import tsConfigPaths from 'vite-tsconfig-paths'
import { tanstackStart } from '@tanstack/react-start/plugin/vite'
import react from '@vitejs/plugin-react'

const __dirname = path.dirname(fileURLToPath(import.meta.url))

export default defineConfig(() => ({
  server: {
    port: 3000,
  },
  preview: {
    port: 3000,
  },
  plugins: [
    tsConfigPaths(),
    ...(process.env.VITEST
      ? [react()]
      : [tanstackStart({ spa: { enabled: true } }), react()]),
  ],
  resolve: {
    alias: process.env.VITEST
      ? {
          'monaco-editor': path.resolve(__dirname, 'src/editor/__mocks__/monaco-editor.ts'),
        }
      : undefined,
  },
  test: {
    environment: 'jsdom',
    globals: true,
    include: ['src/**/*.{test,spec}.{ts,tsx}'],
  },
}))
