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
  await expect(page.getByTestId('node-source-3')).toBeVisible()
  await page.getByTestId('run-scenario-btn').click()
  await expect(page.getByTestId('status-text')).toContainText('Bridge scenario completed', {
    timeout: 30_000,
  })
  await expect(page.getByTestId('subscription-id')).not.toContainText('none')
  await expect(page.getByTestId('result-handle')).not.toContainText('none')
  await expect(page.getByTestId('notification-log')).toContainText('snaqlite/publishNodeResult')
})

test('editing node source pushes dependent updates without manual resubscribe', async ({ page }) => {
  await page.goto('/')
  await page.getByTestId('canvas-id-input').fill('canvas-e2e-edit')
  await page.getByTestId('run-scenario-btn').click()
  await expect(page.getByTestId('status-text')).toContainText('Bridge scenario completed', {
    timeout: 30_000,
  })
  await expect(page.getByTestId('node-result-status')).toContainText('snaq://canvas-e2e-edit-recovered/node-2.sl')
  await expect(page.getByTestId('node-result-status')).toContainText('snaq://canvas-e2e-edit-recovered/node-3.sl')
  await page.getByTestId('node-source-1').fill('[9, 10, 11, 12]')
  await expect(page.getByTestId('subscription-id')).not.toContainText('none')
  await expect(page.getByTestId('notification-log')).toContainText('snaqlite/publishNodeResult')
  await expect(page.getByTestId('node-result-status')).toContainText('node-3.sl: Completed')
})

test('connect and disconnect drive node result status transitions', async ({ page }) => {
  await page.goto('/')
  await page.getByTestId('canvas-id-input').fill('canvas-e2e-disconnect')
  await page.getByTestId('run-scenario-btn').click()
  await expect(page.getByTestId('status-text')).toContainText('Bridge scenario completed', {
    timeout: 30_000,
  })
  await page.getByTestId('disconnect-nodes-btn').click()
  await expect(page.getByTestId('status-text')).not.toContainText('canvas mismatch')
  await expect(page.getByTestId('notification-log')).toContainText('snaqlite/publishNodeResult')
})

test('slice pagination uses continuation flow', async ({ page }) => {
  await page.goto('/')
  await page.getByTestId('canvas-id-input').fill('canvas-e2e-pagination')
  await page.getByTestId('run-scenario-btn').click()
  await expect(page.getByTestId('status-text')).toContainText('Bridge scenario completed', {
    timeout: 30_000,
  })
  await expect(page.getByTestId('result-handle')).not.toContainText('none')

  await page.getByTestId('fetch-first-slice-btn').click()
  await expect(page.getByTestId('slice-output')).toBeVisible()

  await page.getByTestId('fetch-next-slice-btn').click()
  await expect(page.getByTestId('slice-output')).toBeVisible()
})
