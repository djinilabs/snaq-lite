import { defineConfig, devices } from '@playwright/test'

const baseURL = process.env.PLAYWRIGHT_BASE_URL ?? 'http://localhost:3000'
const reuseServer = !!process.env.PLAYWRIGHT_REUSE_SERVER

export default defineConfig({
  testDir: 'e2e',
  fullyParallel: true,
  forbidOnly: !!process.env.CI,
  retries: process.env.CI ? 2 : 0,
  workers: process.env.CI ? 1 : undefined,
  reporter: [['list'], ['html', { outputFolder: 'test-results/html', open: 'never' }]],
  use: {
    baseURL,
    trace: process.env.CI ? 'on-first-retry' : 'on-first-retry',
    screenshot: 'only-on-failure',
    // Optional: PLAYWRIGHT_SLOW_MO=500 to slow actions (ms) when watching with --headed
    launchOptions: {
      slowMo: Number(process.env.PLAYWRIGHT_SLOW_MO) || 0,
    },
  },
  outputDir: 'test-results/playwright-output',
  ...(reuseServer
    ? {}
    : {
        webServer: {
          command: 'pnpm run preview',
          url: baseURL,
          reuseExistingServer: !process.env.CI,
          timeout: 60_000,
        },
      }),
  projects: [{ name: 'chromium', use: { ...devices['Desktop Chrome'] } }],
})
