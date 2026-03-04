/**
 * Loads a project when entering /project/$projectId. Disposes current models,
 * loads snapshot from storage, setGraph with initialContent, clears widgets.
 * When the snapshot has edges, syncs them to the LSP in the background (didOpen + graph/connect)
 * so the presentation block can subscribe; the graph is set synchronously so blocks always appear
 * even if sync fails or is slow.
 * Handles invalid/missing projectId (redirect to /) and race conditions.
 */

import { useEffect, useRef } from 'react'
import { useNavigate } from '@tanstack/react-router'
import { disposeAllGraphModels } from '~/editor/text-model-registry'
import { getFileBlob } from '~/lib/file-blob-idb'
import { getProjectSnapshot } from '~/lib/project-storage'
import {
  isValidUuid,
  snapshotEdgesToGraphEdges,
  snapshotToGraphNodes,
} from '~/lib/project-loader-utils'
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
      const edges = snapshotEdgesToGraphEdges(snapshot.edges, nodes)
      useGraphStore.getState().setGraph(nodes, edges, { clearHistory: true })
      useWidgetStore.getState().clearAll()
      const hasBlobUrl = nodes.some((n) => n.type === 'file' && n.url?.startsWith('blob:'))
      if (hasBlobUrl) {
        void (async () => {
          try {
            const migrated = await Promise.all(
              nodes.map(async (n) => {
                if (n.type === 'file' && n.url?.startsWith('blob:')) {
                  const blob = await getFileBlob(projectId, n.id)
                  return blob ? { ...n, url: `indexeddb://${projectId}/${n.id}` } : n
                }
                return n
              }),
            )
            useGraphStore.getState().setGraph(migrated, edges, { clearHistory: true })
            if (edges.length > 0) {
              void syncLoadedGraphToLsp(migrated, edges).catch(() => {})
            }
          } catch (err) {
            console.error('[useProjectLoader] Legacy blob URL migration failed', err)
          }
        })()
      } else if (edges.length > 0) {
        void syncLoadedGraphToLsp(nodes, edges).catch(() => {})
      }
    } else {
      useGraphStore.getState().setGraph([], [], { clearHistory: true })
      useWidgetStore.getState().clearAll()
    }
  }, [projectId, navigate])
}
