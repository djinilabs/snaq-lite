import { expect, test } from '@playwright/test'

test('blank home page loads', async ({ page }) => {
  await page.goto('/')
  await expect(page.getByTestId('home-page')).toBeVisible()
})

test('bridge scenario controls are available', async ({ page }) => {
  await page.goto('/')
  await expect(page.getByTestId('init-worker-btn')).toBeVisible()
  await expect(page.getByTestId('run-scenario-btn')).toBeVisible()
  await expect(page.getByTestId('connect-nodes-btn')).toBeVisible()
  await expect(page.getByTestId('subscribe-node-btn')).toBeVisible()
  await expect(page.getByTestId('fetch-first-slice-btn')).toBeVisible()
  await expect(page.getByTestId('fetch-next-slice-btn')).toBeVisible()
})

test('bridge scenario runs end-to-end', async ({ page }) => {
  await page.goto('/')
  await page.getByTestId('canvas-id-input').fill('canvas-e2e')
  await page.getByTestId('run-scenario-btn').click()
  await expect(page.getByTestId('status-text')).toContainText('Bridge scenario completed', {
    timeout: 30_000,
  })
  await expect(page.getByTestId('subscription-id')).not.toContainText('none')
  await expect(page.getByTestId('result-handle')).not.toContainText('none')
  await expect(page.getByTestId('notification-log')).toContainText('snaqlite/publishNodeResult')
})
