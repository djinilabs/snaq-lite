# Remove connections between blocks in the UI

## Overview

Enable users to remove connections (edges) between blocks by making edges selectable and deletable in the React Flow canvas, and ensure the existing onEdgesDelete → disconnectEdge flow works. **E2E tests must cover the new behaviour.**

---

## 1. Implementation (summary)

- **graph-canvas.tsx:** Set `edgesSelectable={true}` and `edgesDeletable={true}` on `<ReactFlow>`; ensure `onEdgesDelete` uses `targetInputIndex` from params.
- **edge-delete-params.ts:** Return `{ targetUri, targetInputIndex }` (parse `targetHandle` as number); update type and tests.
- **Optional:** Toolbar/keyboard delete for selected edges (track `selectedEdgeIds`, extend handleDeleteSelected).

---

## 2. E2E test coverage (required)

The new behaviour **must** be covered by Playwright E2E tests in [apps/frontend/e2e/canvas.spec.ts](apps/frontend/e2e/canvas.spec.ts) (or a dedicated spec if preferred). Reuse the existing wiring helpers and assertions where possible.

### 2.1 Test: Remove connection by selecting edge and pressing Delete

**Goal:** After wiring a computation to a presentation, the user can remove the connection by selecting the edge and pressing Delete (or Backspace); the presentation returns to the “Connect a computation box” state.

**Steps:**

1. **Setup (reuse existing pattern):**
   - `gotoCanvas(page)`
   - Add computation box, focus editor, type `7`, wait for editor/result to settle
   - Add presentation block
   - Assert placeholder: `await expect(page.getByText('Connect a computation box').first()).toBeVisible()`

2. **Wire computation → presentation (same as “wired presentation shows computation value”):**
   - Get `computation-output-handle` and `presentation-input-handle`, compute midpoint or use drag from source to target
   - `page.mouse.move(startX, startY)` → `mouse.down()` → `mouse.move(endX, endY, { steps: 10 })` → `mouse.up()`
   - Wait for connection to settle (e.g. 1500–2500 ms)

3. **Assert connection is present:**
   - `await expect(page.getByTestId('presentation-content').first().getByText('7')).toBeVisible({ timeout: 15_000 })`
   - Optionally assert no “unbound stream input” / placeholder text in presentation content

4. **Select the edge:**
   - **Option A (preferred if supported):** Add a stable `data-testid` to edges in the graph when building flow edges (e.g. `data-testid={`graph-edge-${sourceId}-${targetId}-${targetInputIndex}`}`). In E2E: `page.getByTestId('graph-edge-...').first().click()`. This may require passing a custom edge type or edge options in React Flow that attach the attribute to the edge wrapper/path.
   - **Option B:** Click the midpoint of the edge. Compute midpoint from the two handle positions (source handle center, target handle center) and `page.mouse.click(midX, midY)`. Ensures the click hits the edge for selection.
   - **Option C:** Use React Flow’s default edge class/selector if documented (e.g. `.react-flow__edge` or `[data-id="<edge-id>"]`) and click the first edge. Prefer adding a test id for stability.

5. **Delete the edge:**
   - `await page.keyboard.press('Delete')` (or `Backspace` to match implementation).
   - Ensure focus is on the canvas (e.g. click on graph pane before pressing Delete if needed).

6. **Assert connection is removed:**
   - Presentation shows placeholder again: `await expect(page.getByText('Connect a computation box').first()).toBeVisible({ timeout: 5000 })`
   - Presentation content no longer shows the value: `await expect(page.getByTestId('presentation-content').first().getByText('7')).not.toBeVisible()` (or wait for placeholder and assert no “7” in presentation).

**Timeout:** `test.setTimeout(30_000)` (or 35_000) to allow for wiring and LSP updates.

### 2.2 Optional: Remove connection with Backspace

If both Delete and Backspace are supported, add a short test that uses `page.keyboard.press('Backspace')` instead of `Delete` and asserts the same post-removal state. Can be a second test or a parameterised run.

### 2.3 Implementation notes for E2E

- **Edge selector:** If the codebase does not yet add `data-testid` to edges, implement it when building edges in [graph-canvas.tsx](apps/frontend/src/components/canvas/graph-canvas.tsx) (e.g. via React Flow’s edge `data` or a custom Edge component that renders with a test id). Use a predictable id format like `graph-edge-${sourceId}-${targetId}-${targetInputIndex}` so the E2E can use `page.getByTestId(/^graph-edge-/).first()` when there is only one edge.
- **Focus:** If Delete/Backspace does not fire when the edge is selected, ensure the graph pane or React Flow container is focusable and receives the key event after the edge click; optionally call `page.getByTestId('graph-canvas-wrapper').click()` before `keyboard.press('Delete')`.
- **Stability:** Reuse the same wait timeouts as in “wired presentation shows computation value” and “wired presentation shows scalar result” to avoid flakiness.

### 2.4 Running and extending

- Run E2E: `pnpm smoketest` or `pnpm smoketest:dev` (with dev server running).
- If adding “Delete selected” for edges (optional implementation), add a test that selects the edge then clicks the toolbar “Delete selected” button and asserts the same outcome.

---

## 3. Files to touch (implementation + E2E)

| File | Change |
|------|--------|
| [apps/frontend/src/components/canvas/graph-canvas.tsx](apps/frontend/src/components/canvas/graph-canvas.tsx) | Add `edgesSelectable={true}`, `edgesDeletable={true}`; ensure edges have a stable `data-testid` for E2E (e.g. via edge `data` or custom edge component); ensure `onEdgesDelete` uses `targetInputIndex` from params. |
| [apps/frontend/src/components/canvas/edge-delete-params.ts](apps/frontend/src/components/canvas/edge-delete-params.ts) | Return `targetInputIndex` (number) from parsed `targetHandle`; update `DisconnectParams` type. |
| [apps/frontend/src/components/canvas/edge-delete-params.test.ts](apps/frontend/src/components/canvas/edge-delete-params.test.ts) | Update tests for index-based params. |
| [apps/frontend/e2e/canvas.spec.ts](apps/frontend/e2e/canvas.spec.ts) | Add test “remove connection by selecting edge and pressing Delete” (and optionally Backspace / “Delete selected”) as above. |
| [apps/frontend/src/routes/project.$projectId.tsx](apps/frontend/src/routes/project.$projectId.tsx) | Optional: track selected edges and delete them in handleDeleteSelected + key handler. |
| [apps/frontend/src/components/project-toolbar.tsx](apps/frontend/src/components/project-toolbar.tsx) | Optional: enable “Delete selected” when edges are selected. |

---

## 4. Verification

- **Unit:** edge-delete-params and edge-handlers tests pass; graph-store removeEdge tests pass.
- **E2E:** New test(s) in canvas.spec.ts pass with `pnpm smoketest` / `pnpm smoketest:dev`.
- **Lint/build:** `pnpm test`, `pnpm run lint`, `pnpm build` (frontend) all pass.
