/**
 * Loads a project when entering /project/$projectId. Disposes current models,
 * loads snapshot from storage, setGraph with initialContent, clears widgets.
 * Handles invalid/missing projectId (redirect to /) and race conditions.
 */

import { useEffect, useRef } from 'react'
import { useNavigate } from '@tanstack/react-router'
import { disposeAllGraphModels } from '~/editor/text-model-registry'
import { getProjectSnapshot } from '~/lib/project-storage'
import { isValidUuid, snapshotToGraphNodes } from '~/lib/project-loader-utils'
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
      useGraphStore.getState().setGraph(nodes, edges)
    } else {
      useGraphStore.getState().setGraph([], [])
    }
    useWidgetStore.getState().clearAll()
  }, [projectId, navigate])
}
