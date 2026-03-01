import { test, expect } from '@playwright/test'

test.describe('project list', () => {
  test('shows project list page with New project button', async ({ page }) => {
    await page.goto('/')
    await expect(page.getByTestId('project-list-page')).toBeVisible()
    await expect(page.getByTestId('new-project-btn')).toBeVisible()
    await expect(page.getByTestId('new-project-btn')).toHaveText('New project')
  })

  test('shows Import button and empty state when no projects', async ({ page }) => {
    await page.goto('/')
    await expect(page.getByTestId('import-btn')).toBeVisible()
    await expect(page.getByText('No projects yet', { exact: false })).toBeVisible()
  })

  test('clicking New project navigates to canvas with project UUID', async ({ page }) => {
    await page.goto('/')
    await page.getByTestId('new-project-btn').click()
    await expect(page).toHaveURL(/\/project\/[0-9a-f-]{36}/i)
    await expect(page.getByTestId('canvas-page')).toBeVisible()
    await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
  })

  test('after creating project and going back, list shows one project and Open returns to canvas', async ({
    page,
  }) => {
    await page.goto('/')
    await page.getByTestId('new-project-btn').click()
    await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
    await page.getByTestId('back-to-projects').click()
    await expect(page).toHaveURL('/')
    await expect(page.getByTestId('project-list')).toBeVisible()
    const items = page.getByTestId('project-item')
    await expect(items).toHaveCount(1)
    await items.getByRole('button', { name: 'Open' }).click()
    await expect(page).toHaveURL(/\/project\/[0-9a-f-]{36}/i)
    await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
  })

  test('Delete project from list removes it after confirming', async ({ page }) => {
    await page.goto('/')
    await page.getByTestId('new-project-btn').click()
    await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
    await page.getByTestId('back-to-projects').click()
    await expect(page.getByTestId('project-item')).toHaveCount(1)
    page.once('dialog', (d) => d.accept())
    await page.getByTestId('project-item').getByRole('button', { name: 'Delete' }).click()
    await expect(page.getByText('No projects yet', { exact: false })).toBeVisible()
    await expect(page.getByTestId('project-list-page')).toBeVisible()
    await expect(page.getByTestId('project-item')).toHaveCount(0)
  })

  test('Import valid project file navigates to canvas', async ({ page }) => {
    await page.goto('/')
    await page.getByTestId('import-file-input').setInputFiles('e2e/fixtures/valid-project.snaq.json')
    await expect(page).toHaveURL(/\/project\/[0-9a-f-]{36}/i)
    await expect(page.getByTestId('canvas-page')).toBeVisible()
    await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
  })
})
