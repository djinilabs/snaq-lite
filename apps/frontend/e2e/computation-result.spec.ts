import { test, expect, type Page } from '@playwright/test'

const E2E_LSP_LOG = '__E2E_LSP_LOG__'

/** Navigate to app root and create a new project so the canvas is visible. */
async function gotoCanvas(page: Page): Promise<void> {
  await page.goto('/')
  await page.getByTestId('new-project-btn').click()
  await expect(page).toHaveURL(/\/project\/[0-9a-f-]{36}/i, { timeout: 10_000 })
  await expect(page.getByTestId('canvas-toolbar')).toBeVisible({ timeout: 15_000 })
}

test.describe('computation result (editor–worker–LSP)', () => {
  test.setTimeout(20_000)

  test('debug: capture LSP log and console when typing 42', async ({ page }) => {
    const consoleLogs: string[] = []
    page.on('console', (msg) => {
      const text = msg.text()
      const type = msg.type()
      consoleLogs.push(`[${type}] ${text}`)
    })
    await page.addInitScript(() => {
      const w = window as unknown as Record<string, unknown>
      w['__E2E_LSP_LOG__'] = [] as Array<{ dir: string; method: string; params?: unknown }>
      w['__E2E_WORKER_MESSAGES__'] = [] as string[]
    })
    await gotoCanvas(page)
    // Wait for LSP to become ready (worker + WASM load)
    const lspReady = await page.evaluate(() => {
      return new Promise<boolean>((resolve) => {
        const deadline = Date.now() + 10_000
        const check = () => {
          const w = window as unknown as { __E2E_LSP_READY__?: boolean }
          if (w.__E2E_LSP_READY__ === true) {
            resolve(true)
            return
          }
          if (Date.now() >= deadline) {
            resolve(false)
            return
          }
          setTimeout(check, 200)
        }
        check()
      })
    })
    console.log('--- E2E debug: LSP ready within 10s? ---', lspReady)
    await page.getByTestId('add-computation-btn').click()
    const editorZone = page.getByTestId('computation-editor-zone').first()
    await expect(editorZone).toBeVisible({ timeout: 10_000 })
    await page.evaluate((key) => {
      const w = window as unknown as Record<string, unknown>
      if (Array.isArray(w[key])) w[key] = []
    }, E2E_LSP_LOG)
    await editorZone.click()
    await page.waitForTimeout(200)
    await page.keyboard.type('42')
    await page.waitForTimeout(5_000)

    const debug = await page.evaluate(() => {
      const w = window as unknown as Record<string, unknown>
      return {
        lspLog: (w.__E2E_LSP_LOG__ as Array<{ dir: string; method: string; params?: unknown }>) ?? [],
        lspReady: w.__E2E_LSP_READY__,
        workerError: w.__E2E_LSP_WORKER_ERROR__,
        workerErrorEvent: w.__E2E_LSP_WORKER_ERROR_EVENT__,
        workerErrorLast: w.__E2E_WORKER_ERROR_LAST__,
        workerMessages: (w.__E2E_WORKER_MESSAGES__ as string[]) ?? [],
      }
    })
    const resultHtml = await page.getByTestId('computation-result').first().innerHTML()
    const has42 = await page.getByTestId('computation-result').first().getByText('42').count() > 0

    console.log('--- E2E debug: __E2E_LSP_READY__ ---', debug.lspReady)
    console.log('--- E2E debug: __E2E_LSP_WORKER_ERROR__ (from worker message) ---', debug.workerError)
    console.log('--- E2E debug: __E2E_LSP_WORKER_ERROR_EVENT__ (worker.onerror) ---', debug.workerErrorEvent)
    console.log('--- E2E debug: __E2E_WORKER_ERROR_LAST__ (worker.onerror JSON) ---', debug.workerErrorLast)
    console.log('--- E2E debug: __E2E_WORKER_MESSAGES__ (raw from worker, count) ---', (debug.workerMessages as string[]).length)
    ;(debug.workerMessages as string[]).forEach((m, i) => console.log(`  [${i}] ${m.slice(0, 200)}${m.length > 200 ? '...' : ''}`))
    console.log('--- E2E debug: LSP log ---')
    console.log(JSON.stringify(debug.lspLog, null, 2))
    console.log('--- E2E debug: computation-result innerHTML ---')
    console.log(resultHtml)
    console.log('--- E2E debug: has "42" in result? ---', has42)
    console.log('--- E2E debug: console messages (last 50) ---')
    consoleLogs.slice(-50).forEach((l) => console.log(l))
  })

  test('computation block shows result after typing expression', async ({ page }) => {
    await gotoCanvas(page)
    await expect(page.getByTestId('computation-node')).toHaveCount(0)
    await page.getByTestId('add-computation-btn').click()
    await expect(page.getByTestId('computation-node')).toHaveCount(1)

    const editorZone = page.getByTestId('computation-editor-zone').first()
    await expect(editorZone).toBeVisible({ timeout: 10_000 })
    await editorZone.click()
    await page.waitForTimeout(200)
    await page.keyboard.type('4')
    await page.waitForTimeout(400)
    await page.keyboard.type('2')
    await page.waitForTimeout(2500)

    await expect(
      page.getByTestId('computation-result').first().getByText('42'),
    ).toBeVisible({ timeout: 15_000 })
  })

  test('protocol: didOpen, subscribeWidget, widgetDataUpdate over worker', async ({ page }) => {
    await page.addInitScript(() => {
      ;(window as unknown as Record<string, unknown>)[
        '__E2E_LSP_LOG__' as string
      ] = [] as Array<{ dir: string; method: string; params?: unknown }>
    })
    await gotoCanvas(page)
    await page.getByTestId('add-computation-btn').click()
    const editorZone = page.getByTestId('computation-editor-zone').first()
    await expect(editorZone).toBeVisible({ timeout: 10_000 })
    await page.evaluate((key) => {
      const w = window as unknown as Record<string, unknown>
      if (Array.isArray(w[key])) w[key] = []
    }, E2E_LSP_LOG)
    await editorZone.click()
    await page.waitForTimeout(200)
    await page.keyboard.type('4')
    await page.waitForTimeout(400)
    await page.keyboard.type('2')
    await page.waitForTimeout(2500)
    await expect(
      page.getByTestId('computation-result').first().getByText('42'),
    ).toBeVisible({ timeout: 15_000 })

    const log = await page.evaluate((key) => {
      const w = window as unknown as Record<string, Array<{ dir: string; method: string; params?: unknown }>>
      return w[key] ?? []
    }, E2E_LSP_LOG)

    const out = (m: string) => log.some((e) => e.dir === 'out' && e.method === m)
    const in_ = (m: string) => log.some((e) => e.dir === 'in' && e.method === m)
    expect(out('textDocument/didOpen'), 'log should contain didOpen (out)').toBe(true)
    expect(out('snaqlite/graph/subscribeWidget'), 'log should contain subscribeWidget (out)').toBe(true)
    expect(in_('snaqlite/graph/widgetDataUpdate'), 'log should contain widgetDataUpdate (in)').toBe(true)
    const widgetUpdate = log.find(
      (e) => e.dir === 'in' && e.method === 'snaqlite/graph/widgetDataUpdate',
    )
    expect(widgetUpdate?.params).toBeDefined()
    expect((widgetUpdate?.params as { status?: string })?.status).toBe('Completed')
  })
})
