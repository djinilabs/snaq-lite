# Agent UI workflow

This doc describes how to run the app for observation, run smoke tests, and use the browser MCP so an agent can observe the UI, detect issues, implement fixes, and verify them.

## Running the app

- **Dev server:** From repo root: `pnpm dev` (or `pnpm run dev:frontend`). App at http://localhost:3000.
- **Preview (built):** `pnpm run build:frontend` then `pnpm preview` (or root `pnpm preview`). Serves the built app.

## Smoke test commands

Use **pnpm** (this repo does not use npm for scripts). If using the run-smoke-tests skill, use the pnpm commands below instead of `npm run smoketest`.

- **From repo root**
  - `pnpm smoketest` — Builds frontend, then runs Playwright with webServer (starts `vite preview`). Use for CI or one-shot check.
  - `pnpm smoketest:dev` — Runs Playwright only; **requires** the app already running (e.g. `pnpm dev` in another terminal). Uses `PLAYWRIGHT_REUSE_SERVER=1` so no webServer is started. Faster for local iteration.
- **From apps/frontend**
  - `pnpm run smoketest` — Same as root smoketest but assumes you already built (or run from root for full flow).
  - `pnpm run smoketest:dev` — Same as root smoketest:dev; dev server must be running.

**Single command:** From repo root, **`pnpm smoketest`** prepares the environment (frontend deps + Playwright Chromium), builds the frontend, starts the preview server, runs E2E tests, and stops the server when tests finish. No separate sandbox or bootstrap is needed.

If port 3000 is already in use, either stop the other process or set `PLAYWRIGHT_BASE_URL` and use `pnpm smoketest:dev` with the app already running. For local-only browser install (no system deps): `pnpm -C apps/frontend exec playwright install chromium`.

## Taking a screenshot the agent can read

When using the browser MCP to judge layout/contrast/alignment:

1. Save screenshots under the **workspace** so the Read tool can open them. Use the root-level directory **`e2e-artifacts/`** (e.g. `e2e-artifacts/agent-view.png`). The MCP `browser_take_screenshot` tool accepts a `filename`; if it resolves relative to the workspace, that path works. If the MCP saves only to a fixed location (e.g. `~/.cursor/browser-logs/`), the agent can still Read from that path if it is accessible.
2. After taking the screenshot, use the Read tool on the image path to inspect the UI.

## Browser MCP workflow (observe → interact → verify)

1. **Start the app** (if not already): `pnpm dev` or `pnpm preview`.
2. **Lock and navigate**
   - If a browser tab already exists: call **`browser_lock`** first, then interact.
   - If not: **`browser_navigate`** to `http://localhost:3000` (or your base URL), then **`browser_lock`** before any interactions.
3. **Observe**
   - **`browser_snapshot`** — Structure and element refs for clicking/typing.
   - **`browser_take_screenshot`** with filename in `e2e-artifacts/` — For pixel-level review via Read.
4. **Interact** — `browser_click`, `browser_type`, `browser_fill`, etc. Snapshot or screenshot again to verify.
5. **Unlock** — **`browser_unlock`** when done.

## Detect → implement → review

- **Detect:** Run `pnpm smoketest` or `pnpm smoketest:dev`; on failure, open the Playwright HTML report and traces. Optionally use the browser MCP to reproduce and take a screenshot to `e2e-artifacts/` and Read it.

**Note:** Current smoke tests do not depend on LSP/WASM (no editor or widget output assertions). Full canvas flows (e.g. typing in a computation box and seeing results in a presentation block) may require `pnpm run build:lsp-wasm` and can be covered in a later test expansion.
- **Implement:** Edit code in `apps/frontend` (and root scripts if needed). Follow memory/systemPatterns.md and .cursorrules (unit tests, lint, build).
- **Review:** Run `pnpm test`, `pnpm run lint`, `pnpm build`, and `pnpm smoketest` as appropriate. Confirm all pass before claiming done.
