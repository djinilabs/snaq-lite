/**
 * Loads a project when entering /project/$projectId. Disposes current models,
 * loads snapshot from storage, setGraph with initialContent, clears widgets.
 * When the snapshot has edges, syncs them to the LSP (didOpen + graph/connect) before
 * setGraph so the presentation block does not see "unbound stream input" when it subscribes.
 * Handles invalid/missing projectId (redirect to /) and race conditions.
 */

import { useEffect, useRef } from 'react'
import { useNavigate } from '@tanstack/react-router'
import { disposeAllGraphModels } from '~/editor/text-model-registry'
import { getProjectSnapshot } from '~/lib/project-storage'
import { isValidUuid, snapshotToGraphNodes } from '~/lib/project-loader-utils'
import { syncLoadedGraphToLsp } from '~/lib/sync-graph-to-lsp'
import { useGraphStore } from '~/store'
import { useProjectsIndexStore } from '~/store'
import { useWidgetStore } from '~/store'

export function useProjectLoader(projectId: string): void {
  const navigate = useNavigate()
  const lastLoadedProjectIdRef = useRef<string | null>(null)

  useEffect(() => {
    if (!projectId || !isValidUuid(projectId)) {
      navigate({ to: '/' })
      return
    }

    const hydrated = useProjectsIndexStore.getState().hydrated
    if (!hydrated) {
      useProjectsIndexStore.getState().hydrate()
    }
    const indexAfterHydrate = useProjectsIndexStore.getState().projects
    const inIndex = indexAfterHydrate.some((p) => p.id === projectId)

    const snapshot = getProjectSnapshot(projectId)
    if (!snapshot && !inIndex) {
      navigate({ to: '/' })
      return
    }

    // Avoid overwriting the graph when effect re-runs for the same project (e.g. React Strict Mode in dev).
    if (lastLoadedProjectIdRef.current === projectId) {
      return
    }
    lastLoadedProjectIdRef.current = projectId

    const currentNodes = useGraphStore.getState().nodes
    disposeAllGraphModels(currentNodes.map((n) => n.id))

    if (snapshot) {
      const nodes = snapshotToGraphNodes(snapshot)
      const edges = snapshot.edges

      if (edges.length > 0) {
        let cancelled = false
        syncLoadedGraphToLsp(nodes, edges).then(() => {
          if (!cancelled) {
            useGraphStore.getState().setGraph(nodes, edges, { clearHistory: true })
            useWidgetStore.getState().clearAll()
          }
        })
        return () => {
          cancelled = true
        }
      }

      useGraphStore.getState().setGraph(nodes, edges, { clearHistory: true })
    } else {
      useGraphStore.getState().setGraph([], [], { clearHistory: true })
    }
    useWidgetStore.getState().clearAll()
  }, [projectId, navigate])
}
