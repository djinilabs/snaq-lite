# Canvas Runtime Orchestration

This document describes the expected UI orchestration flow when driving the LSP as a canvas runtime.

## Lifecycle

1. Initialize worker and LSP (`initialize` + `initialized`).
2. Bootstrap runtime state (`snaqlite/bootstrapSession`).
3. If canvas differs and runtime is not drained, reset/import as needed.
4. Open node documents with canonical `snaq://<canvasId>/...` URIs.
5. Mutate graph/source through `snaqlite/graph/applyPatch` (atomic wave).
6. Subscribe to node outputs with `snaqlite/subscribeNode`.
7. Render `snaqlite/publishNodeResult` updates.
8. Fetch paged details on demand with `snaqlite/graph/fetchResultSlice`.

## Patch Wave Rules

- `graph/applyPatch` is the canonical mutation entrypoint for canvas edits.
- Operations in one patch are staged and committed atomically.
- Supported operations:
  - `addNode`, `removeNode`
  - `setNodeSource`
  - `connect`, `disconnect`
  - `renameParam`, `addParam`, `removeParam`
- Mutation waves for canvas URIs force descendant reevaluation so downstream nodes refresh even after non-semantic source edits.

## Result Transport

- Node updates are published through `snaqlite/publishNodeResult`.
- `Completed` payloads include summaries and optional `resultHandle`.
- Large vectors/maps are not eagerly materialized in notifications.
- UI requests slices lazily with `fetchResultSlice` using:
  - `resultHandle`
  - `path` (for nested vectors/maps)
  - `offset` + `limit`
  - optional continuation `cursor`

## Cancellation Semantics

- `didClose`: subscriptions/widgets receive `Cancelled` (`Document closed`).
- `resetNamespace`: matching subscriptions/widgets receive `Cancelled` (`Namespace reset`).
- `importCanvasDocument`: active subscriptions/widgets receive `Cancelled` (`Canvas import`).
- `removeNode` in patch lifecycle: affected subscriptions/widgets receive `Cancelled` (`Node removed`).

## UI State Recommendations

- Keep node params source-authoritative from `graph/nodeSignatureUpdated`.
- Track node subscriptions per URI, not globally.
- Track pagination cursor per `{resultHandle, path}`.
- Treat disconnect refresh failures caused by intentionally unbound inputs as non-fatal UX status.
