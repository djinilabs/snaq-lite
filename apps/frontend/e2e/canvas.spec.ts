import { test, expect, type Page } from '@playwright/test'

/** Navigate to app root and create a new project so the canvas is visible. */
async function gotoCanvas(page: Page): Promise<void> {
  await page.goto('/')
  await page.getByTestId('new-project-btn').click()
  await expect(page).toHaveURL(/\/project\/[0-9a-f-]{36}/i)
  await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
}

test.describe('canvas', () => {
  test('canvas page shows toolbar and graph area after creating project', async ({ page }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('graph-canvas-wrapper')).toBeVisible()
    await expect(page.getByTestId('back-to-projects')).toBeVisible()
    await expect(page.getByTestId('add-computation-btn')).toHaveText('Add computation box')
  })

  test('toolbar shows Save, Export, Add presentation, Delete selected, Rename, Delete project', async ({
    page,
  }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('save-btn')).toBeVisible()
    await expect(page.getByTestId('export-btn')).toBeVisible()
    await expect(page.getByTestId('add-presentation-btn')).toHaveText('Add presentation block')
    await expect(page.getByTestId('delete-selected-btn')).toBeVisible()
    await expect(page.getByTestId('rename-btn')).toBeVisible()
    await expect(page.getByTestId('delete-project-btn')).toBeVisible()
  })

  test('Back to projects returns to project list', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('back-to-projects').click()
    await expect(page).toHaveURL('/')
    await expect(page.getByTestId('project-list-page')).toBeVisible()
  })

  test('Add computation box adds a computation node to the canvas', async ({ page }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
  })

  test('Add presentation block adds a presentation node to the canvas', async ({ page }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('presentation-node')).toHaveCount(0)
    await page.getByTestId('add-presentation-btn').click()
    await expect(page.getByTestId('presentation-node')).toHaveCount(1)
  })

  test('Save button is clickable without error', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await page.getByTestId('save-btn').click()
    await expect(page.getByTestId('canvas-toolbar')).toBeVisible()
  })

  test('Export triggers download with project UUID and .snaq.json filename', async ({ page }) => {
    await gotoCanvas(page)
    const [download] = await Promise.all([
      page.waitForEvent('download'),
      page.getByTestId('export-btn').click(),
    ])
    const filename = download.suggestedFilename()
    expect(filename).toMatch(/^project-[0-9a-f-]+\.snaq\.json$/i)
  })

  test('Delete selected removes selected node from canvas', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    // Newly added node is selected by the app, so Delete selected is enabled
    await page.getByTestId('delete-selected-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
  })

  test('Delete project from canvas navigates to list after confirming', async ({ page }) => {
    await gotoCanvas(page)
    page.once('dialog', (d) => d.accept())
    await page.getByTestId('delete-project-btn').click()
    await expect(page).toHaveURL('/')
    await expect(page.getByTestId('project-list-page')).toBeVisible()
  })

  test('Rename project and see name on list after going back', async ({ page }) => {
    await gotoCanvas(page)
    const newName = 'E2E Renamed Project'
    page.once('dialog', (d) => d.accept(newName))
    await page.getByTestId('rename-btn').click()
    await page.getByTestId('back-to-projects').click()
    await expect(page).toHaveURL('/')
    await expect(page.getByTestId('project-list-page')).toBeVisible()
    await expect(page.getByText(newName, { exact: false })).toBeVisible()
  })
})
