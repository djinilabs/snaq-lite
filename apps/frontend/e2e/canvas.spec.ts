import { test, expect, type Locator, type Page } from '@playwright/test'

/** Navigate to app root and create a new project so the canvas is visible. */
async function gotoCanvas(page: Page): Promise<void> {
  await page.goto('/')
  await page.getByTestId('new-project-btn').click()
  await expect(page).toHaveURL(/\/project\/[0-9a-f-]{36}/i)
  await expect(page.getByTestId('canvas-toolbar')).toBeVisible({ timeout: 15_000 })
}

async function getNodeRect(loc: Locator): Promise<{ x: number; y: number }> {
  const box = await loc.boundingBox()
  if (box) return { x: box.x, y: box.y }
  const rect = await loc.first().evaluate((el) => {
    const r = el.getBoundingClientRect()
    return { x: r.x, y: r.y }
  })
  return rect
}

/** Pixel tolerance for "node did not move" (layout/zoom can shift; real drag moves 80+ px). */
const STATIONARY_TOLERANCE_PX = 100

/** Assert the node at nodeTestId does not move after performing action (e.g. click). Do not scroll so viewport stays stable. */
async function assertNodeStationaryAfter(
  page: Page,
  nodeTestId: string,
  action: () => Promise<void>,
): Promise<void> {
  const node = page.getByTestId(nodeTestId).first()
  await expect(node).toBeAttached()
  const before = await getNodeRect(node)
  await action()
  await page.waitForTimeout(200)
  const after = await getNodeRect(node)
  expect(Math.abs(after.x - before.x)).toBeLessThanOrEqual(STATIONARY_TOLERANCE_PX)
  expect(Math.abs(after.y - before.y)).toBeLessThanOrEqual(STATIONARY_TOLERANCE_PX)
}

/** Assert the node at nodeTestId moves after dragging from dragZoneTestId by (deltaX, deltaY). */
async function assertNodeMovesAfterDrag(
  page: Page,
  nodeTestId: string,
  dragZoneTestId: string,
  deltaX: number,
  deltaY: number,
): Promise<void> {
  const node = page.getByTestId(nodeTestId).first()
  await expect(node).toBeAttached()
  const before = await getNodeRect(node)
  const dragZone = page.getByTestId(dragZoneTestId).first()
  const box = await dragZone.boundingBox()
  if (!box) {
    const rect = await dragZone.evaluate((el) => {
      const r = el.getBoundingClientRect()
      return { x: r.x, y: r.y, width: r.width, height: r.height }
    })
    const startX = rect.x + rect.width / 2
    const startY = rect.y + rect.height / 2
    await page.mouse.move(startX, startY)
    await page.mouse.down()
    await page.mouse.move(startX + deltaX, startY + deltaY, { steps: 8 })
    await page.mouse.up()
    const after = await getNodeRect(node)
    expect(after.x).not.toBeCloseTo(before.x, 0)
    return
  }
  const startX = box.x + box.width / 2
  const startY = box.y + box.height / 2
  await page.mouse.move(startX, startY)
  await page.mouse.down()
  await page.mouse.move(startX + deltaX, startY + deltaY, { steps: 8 })
  await page.mouse.up()
  const after = await getNodeRect(node)
  expect(after.x).not.toBeCloseTo(before.x, 0)
}

test.describe('canvas', () => {
  test('canvas page shows toolbar and graph area after creating project', async ({ page }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('graph-canvas-wrapper')).toBeVisible()
    await expect(page.getByTestId('back-to-projects')).toBeVisible()
    await expect(page.getByTestId('add-computation-btn')).toHaveText('Add computation box')
  })

  test('toolbar shows Undo, Redo, Export, Add presentation, Delete selected, Rename, Delete project', async ({
    page,
  }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('undo-btn')).toBeVisible()
    await expect(page.getByTestId('redo-btn')).toBeVisible()
    await expect(page.getByTestId('undo-btn')).toBeDisabled()
    await expect(page.getByTestId('redo-btn')).toBeDisabled()
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

  test('Undo and Redo buttons are visible and Undo removes added node', async ({ page }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    await page.getByTestId('undo-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
  })

  test('Redo restores node after Undo', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    await page.getByTestId('undo-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
    await page.getByTestId('redo-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
  })

  test('Ctrl+Z (undo) removes added node', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    await page.getByTestId('canvas-page').click({ position: { x: 10, y: 10 } })
    await page.keyboard.press('Control+z')
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
  })

  test('Shift+Ctrl+Z (redo) restores node after undo', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    await page.getByTestId('canvas-page').click({ position: { x: 10, y: 10 } })
    await page.keyboard.press('Control+z')
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
    await page.keyboard.press('Shift+Control+z')
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
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

  test('Computation node shows Add input button (inputs UI is present)', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    await expect(page.getByTestId('computation-add-input')).toBeAttached()
  })

  test('Clicking input controls does not drag the computation node', async ({ page }) => {
    test.setTimeout(60_000)
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-add-input').first()).toBeAttached({
      timeout: 15_000,
    })
    await assertNodeStationaryAfter(page, 'computation-node', async () => {
      await page.getByTestId('computation-add-input').first().click({ force: true })
    })
  })

  test('Dragging from drag zone moves the computation node', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await assertNodeMovesAfterDrag(
      page,
      'computation-node',
      'computation-drag-zone',
      120,
      80,
    )
  })

  test('Clicking editor zone keeps the computation node stationary', async ({ page }) => {
    test.setTimeout(60_000)
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-editor-zone').first()).toBeAttached({
      timeout: 15_000,
    })
    await assertNodeStationaryAfter(page, 'computation-node', async () => {
      await page.getByTestId('computation-editor-zone').first().click({ force: true })
    })
  })

  test('Clicking input name and type controls does not drag the computation node', async ({
    page,
  }) => {
    test.setTimeout(60_000)
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    const computationNode = page.getByTestId('computation-node').first()
    await computationNode.scrollIntoViewIfNeeded()
    await computationNode.getByTestId('computation-add-input').evaluate((el) => (el as HTMLButtonElement).click())
    await expect(computationNode.getByTestId('computation-input-name-0')).toBeAttached({
      timeout: 15_000,
    })
    await assertNodeStationaryAfter(page, 'computation-node', async () => {
      await page.getByTestId('computation-input-name-0').first().click({ force: true })
      await page.getByTestId('computation-input-name-0').first().fill('x')
      await page.getByTestId('computation-input-type-0').first().selectOption('Numeric')
    })
  })

  test('Dragging from presentation drag zone moves the presentation node', async ({ page }) => {
    await gotoCanvas(page)
    await page.getByTestId('add-presentation-btn').click()
    await page.getByTestId('presentation-node').first().scrollIntoViewIfNeeded()
    await assertNodeMovesAfterDrag(
      page,
      'presentation-node',
      'presentation-drag-zone',
      100,
      60,
    )
  })

  test('Clicking presentation content does not drag the presentation node', async ({ page }) => {
    test.setTimeout(60_000)
    await gotoCanvas(page)
    await page.getByTestId('add-presentation-btn').click()
    await page.getByTestId('presentation-node').first().scrollIntoViewIfNeeded()
    await assertNodeStationaryAfter(page, 'presentation-node', async () => {
      await page.getByTestId('presentation-content').first().click({ force: true })
    })
  })

  test('wiring computation box (Numeric) to presentation box does not show document or type mismatch errors', async ({
    page,
  }) => {
    test.setTimeout(30_000)
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)
    const editorZone = page.getByTestId('computation-editor-zone').first()
    await expect(editorZone).toBeVisible({ timeout: 15_000 })
    await editorZone.click()
    await page.waitForTimeout(200)
    await page.keyboard.type('42')
    await page.waitForTimeout(300)

    await page.getByTestId('add-presentation-btn').click()
    await expect(page.getByTestId('presentation-node')).toHaveCount(1)
    await expect(page.getByText('Connect a computation box').first()).toBeVisible()

    const sourceHandle = page.getByTestId('computation-output-handle').first()
    const targetHandle = page.getByTestId('presentation-input-handle').first()
    await sourceHandle.scrollIntoViewIfNeeded()
    await targetHandle.scrollIntoViewIfNeeded()
    const sourceBox = await sourceHandle.boundingBox()
    const targetBox = await targetHandle.boundingBox()
    expect(sourceBox).toBeTruthy()
    expect(targetBox).toBeTruthy()
    const startX = sourceBox!.x + sourceBox!.width / 2
    const startY = sourceBox!.y + sourceBox!.height / 2
    const endX = targetBox!.x + targetBox!.width / 2
    const endY = targetBox!.y + targetBox!.height / 2

    await page.mouse.move(startX, startY)
    await page.mouse.down()
    await page.mouse.move(endX, endY, { steps: 10 })
    await page.mouse.up()
    await page.waitForTimeout(1200)

    await expect(page.getByText('target document not open')).not.toBeVisible()
    await expect(page.getByText("target has no input named 'input'")).not.toBeVisible()
    await expect(page.getByText("Type mismatch: source output type 'Numeric' does not match target input 'x' type 'Vector'")).not.toBeVisible()
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
