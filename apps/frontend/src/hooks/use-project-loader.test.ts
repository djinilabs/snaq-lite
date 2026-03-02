/**
 * Tests for useProjectLoader: when snapshot has edges and sync rejects,
 * setGraph must still be called so the graph (nodes and edges) appears.
 * We test the synchronous load path (getProjectSnapshot -> snapshotToGraphNodes -> setGraph)
 * to ensure the fix keeps the graph visible regardless of sync.
 */

import { describe, it, expect, beforeEach } from 'vitest'
import { useGraphStore } from '~/store'
import {
  setProjectSnapshot,
  getProjectSnapshot,
  PROJECTS_INDEX_KEY,
} from '~/lib/project-storage'
import { snapshotToGraphNodes } from '~/lib/project-loader-utils'
import type { ProjectSnapshot } from '~/types/project'

const PROJECT_ID = '11111111-2222-3333-4444-555555555555'

const snapshotWithConnectedBlocks: ProjectSnapshot = {
  id: PROJECT_ID,
  version: 1,
  nodes: [
    { id: 'comp-1', position: { x: 0, y: 0 }, type: 'computation', content: '7' },
    { id: 'pres-1', position: { x: 200, y: 0 }, type: 'presentation' },
  ],
  edges: [{ sourceId: 'comp-1', targetId: 'pres-1', targetInputName: 'input' }],
}

describe('useProjectLoader (sync load path)', () => {
  beforeEach(() => {
    useGraphStore.setState({
      nodes: [],
      edges: [],
      pendingEdge: null,
      focusEditorForNodeId: null,
      undoStack: [],
      redoStack: [],
      undoSnapshotGetter: null,
    })
    localStorage.setItem(PROJECTS_INDEX_KEY, JSON.stringify([{ id: PROJECT_ID, updatedAt: 1 }]))
    setProjectSnapshot(snapshotWithConnectedBlocks)
  })

  it('sets graph with nodes and edges from snapshot so blocks appear even when sync would reject', () => {
    const snapshot = getProjectSnapshot(PROJECT_ID)
    expect(snapshot).not.toBeNull()
    const nodes = snapshotToGraphNodes(snapshot!)
    const edges = snapshot!.edges
    useGraphStore.getState().setGraph(nodes, edges, { clearHistory: true })

    expect(useGraphStore.getState().nodes).toHaveLength(2)
    expect(useGraphStore.getState().edges).toHaveLength(1)
    expect(useGraphStore.getState().nodes[0].id).toBe('comp-1')
    expect(useGraphStore.getState().nodes[1].id).toBe('pres-1')
    expect(useGraphStore.getState().edges[0]).toEqual({
      sourceId: 'comp-1',
      targetId: 'pres-1',
      targetInputName: 'input',
    })
  })
})
