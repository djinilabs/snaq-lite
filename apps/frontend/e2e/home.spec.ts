import { expect, test } from '@playwright/test'

test('blank home page loads', async ({ page }) => {
  await page.goto('/')
  await expect(page.getByTestId('home-page')).toBeVisible()
})
