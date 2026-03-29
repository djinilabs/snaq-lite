import { createFileRoute } from '@tanstack/react-router'
import { useEffect, useMemo, useRef, useState } from 'react'
import { createLspClient, type LspClient } from '../lsp/client'
import LspWorker from '../lsp/lsp.worker?worker'
import {
  buildPatchForAddParam,
  buildNodeSource,
  buildPatchForRemoveParam,
  buildPatchForRenameParam,
  type CanvasEdge,
  type CanvasNode,
} from '../lsp/graph-patch'
import { fetchFirstPage, fetchNextPage, type PageCursor } from '../lsp/pagination'
import { ensureCanvasSession } from '../lsp/session-orchestrator'
import {
  connectCanvasNodes,
  disconnectCanvasNodeInput,
  openCanvasNodes,
  patchCanvasNodeSource,
  toCanvasUri,
} from '../lsp/canvas-runtime'
import {
  addCanvasNode,
  removeCanvasEdge,
  removeCanvasNode,
  upsertCanvasEdge,
  type CanvasDocumentState,
} from '../canvas/document-state'
import type {
  NodeSignatureUpdatedParams,
  PublishNodeResultParams,
  WidgetDataUpdateParams,
} from '../lsp/types'
import {
  applyNodeSignatureUpdated,
  applyPublishNodeResult,
  resolveNodeUriFromPublish,
  upsertNodeSubscription,
} from '../lsp/node-runtime-state'
import {
  cursorKey,
  registerNodeSubscription,
  removeNodeSubscriptionByUri,
} from '../lsp/subscription-manager'

export const Route = createFileRoute('/')({
  component: HomePage,
})

function HomePage() {
  const [canvasId, setCanvasId] = useState('canvas-a')
  const [status, setStatus] = useState('Idle')
  const [notifications, setNotifications] = useState<string[]>([])
  const [nodes, setNodes] = useState<CanvasNode[]>([
    {
      uri: 'snaq://canvas-a/node-1.sl',
      source: '[1, 2, 3, 4, 5]',
      params: [],
    },
    {
      uri: 'snaq://canvas-a/node-2.sl',
      source: '$x',
      params: [{ name: 'x', paramId: 'p1', typeName: 'Vector' }],
    },
    {
      uri: 'snaq://canvas-a/node-3.sl',
      source: '$y',
      params: [{ name: 'y', paramId: 'p1', typeName: 'Vector' }],
    },
  ])
  const [edges, setEdges] = useState<CanvasEdge[]>([])
  const [selectedNodeUri, setSelectedNodeUri] = useState('snaq://canvas-a/node-1.sl')
  const [selectedSourceUri, setSelectedSourceUri] = useState('snaq://canvas-a/node-1.sl')
  const [selectedTargetUri, setSelectedTargetUri] = useState('snaq://canvas-a/node-2.sl')
  const [selectedTargetParamId, setSelectedTargetParamId] = useState('p1')
  const [resultHandle, setResultHandle] = useState<string>()
  const [slice, setSlice] = useState<string>('[]')
  const [newParamName, setNewParamName] = useState('x2')
  const paginationRef = useRef<PageCursor>({ offset: 0 })
  const paginationByHandlePathRef = useRef<Record<string, PageCursor>>({})
  const clientRef = useRef<LspClient | null>(null)
  const syncTimersRef = useRef<Record<string, ReturnType<typeof setTimeout>>>({})
  const [nodeSubscriptionsByUri, setNodeSubscriptionsByUri] = useState<
    Record<string, { subscriptionId: string; resultHandle?: string }>
  >({})
  const nodeSubscriptionsRef = useRef<Record<string, { subscriptionId: string; resultHandle?: string }>>({})
  const subscriptionUriByIdRef = useRef<Record<string, string>>({})
  const [nodeResultsByUri, setNodeResultsByUri] = useState<
    Record<
      string,
      {
        status: string
        revision?: number
        payload?: Record<string, unknown>
      }
    >
  >({})
  const nodeResultsRef = useRef<
    Record<
      string,
      {
        status: string
        revision?: number
        payload?: Record<string, unknown>
      }
    >
  >({})
  const canvasIdRef = useRef(canvasId)
  const nodesRef = useRef(nodes)
  const wasmUrl = useMemo(() => {
    if (typeof window === 'undefined') {
      return '/lsp-wasm/snaq_lite_lsp.js'
    }
    return `${window.location.origin}${import.meta.env.BASE_URL}lsp-wasm/snaq_lite_lsp.js`
  }, [])

  useEffect(() => {
    return () => {
      for (const timerId of Object.values(syncTimersRef.current)) {
        clearTimeout(timerId)
      }
      syncTimersRef.current = {}
    }
  }, [])

  useEffect(() => {
    nodeSubscriptionsRef.current = nodeSubscriptionsByUri
  }, [nodeSubscriptionsByUri])

  useEffect(() => {
    nodeResultsRef.current = nodeResultsByUri
  }, [nodeResultsByUri])

  useEffect(() => {
    canvasIdRef.current = canvasId
  }, [canvasId])

  useEffect(() => {
    nodesRef.current = nodes
  }, [nodes])

  useEffect(() => {
    if (!nodes.some((node) => node.uri === selectedNodeUri) && nodes[0]) {
      setSelectedNodeUri(nodes[0].uri)
    }
    if (!nodes.some((node) => node.uri === selectedSourceUri) && nodes[0]) {
      setSelectedSourceUri(nodes[0].uri)
    }
    if (!nodes.some((node) => node.uri === selectedTargetUri) && nodes[1]) {
      setSelectedTargetUri(nodes[1].uri)
    }
  }, [nodes, selectedNodeUri, selectedSourceUri, selectedTargetUri])

  useEffect(() => {
    const params = nodes.find((node) => node.uri === selectedTargetUri)?.params ?? []
    if (params.length === 0) {
      setSelectedTargetParamId('p1')
      return
    }
    if (!params.some((param) => param.paramId === selectedTargetParamId)) {
      setSelectedTargetParamId(params[0].paramId)
    }
  }, [nodes, selectedTargetUri, selectedTargetParamId])

  function handlePublishNodeResult(notificationParams: unknown): void {
    const params = (notificationParams ?? {}) as PublishNodeResultParams
    if (!params.subscriptionId) {
      return
    }
    const uri = resolveNodeUriFromPublish(params, subscriptionUriByIdRef.current)
    if (!uri) {
      return
    }
    const publishUpdate = applyPublishNodeResult(
      nodeResultsRef.current,
      nodeSubscriptionsRef.current,
      uri,
      params,
    )
    nodeResultsRef.current = publishUpdate.nextResults
    nodeSubscriptionsRef.current = publishUpdate.nextSubscriptions
    setNodeResultsByUri(publishUpdate.nextResults)
    setNodeSubscriptionsByUri(publishUpdate.nextSubscriptions)
    if (publishUpdate.resultHandle) {
      const activeTargetNode = nodesRef.current[nodesRef.current.length - 1]
      if (!activeTargetNode) {
        return
      }
      const activeTargetUri = canvasUri(activeTargetNode.uri, canvasIdRef.current)
      setResultHandle((current) => (uri === activeTargetUri ? publishUpdate.resultHandle : current))
    }
  }

  function handleWidgetDataUpdate(notificationParams: unknown): void {
    const params = (notificationParams ?? {}) as WidgetDataUpdateParams
    if (!params.uri) {
      return
    }
    setNodeResultsByUri((current) => ({
      ...current,
      [params.uri as string]: {
        status: params.status,
        revision: params.revision,
        payload: params.payload,
      },
    }))
  }

  function handleNodeSignatureUpdated(notificationParams: unknown): void {
    const params = (notificationParams ?? {}) as NodeSignatureUpdatedParams
    if (!params.uri || !Array.isArray(params.inputs)) {
      return
    }
    setNodes((current) => {
      const next = applyNodeSignatureUpdated(current, params)
      nodesRef.current = next
      return next
    })
  }

  async function initClient() {
    if (clientRef.current) {
      return
    }
    const client = createLspClient({
      wasmUrl,
      workerFactory: () => new LspWorker(),
    })
    client.onNotification((notification) => {
      setNotifications((current) => [...current.slice(-20), notification.method])
      if (notification.method === 'snaqlite/publishNodeResult') {
        handlePublishNodeResult(notification.params)
      }
      if (notification.method === 'snaqlite/graph/widgetDataUpdate') {
        handleWidgetDataUpdate(notification.params)
      }
      if (notification.method === 'snaqlite/graph/nodeSignatureUpdated') {
        handleNodeSignatureUpdated(notification.params)
      }
    })
    await client.initialize()
    clientRef.current = client
    setStatus('Worker initialized')
  }

  async function openNodesInLsp(targetCanvasId: string) {
    const client = clientRef.current
    if (!client) {
      throw new Error('LSP client not initialized')
    }
    await openCanvasNodes(client, nodes, targetCanvasId)
  }

  function canvasUri(uri: string, targetCanvasId: string): string {
    return toCanvasUri(uri, targetCanvasId)
  }

  function optimisticParamUpdate(
    applyUpdate: (current: CanvasNode[]) => CanvasNode[],
    rollbackUpdate: (current: CanvasNode[], optimisticBase: CanvasNode[]) => CanvasNode[],
  ): { rollback: () => void } {
    let optimisticBase: CanvasNode[] | null = null
    setNodes((current) => {
      optimisticBase = current
      return applyUpdate(current)
    })
    return {
      rollback: () => {
        if (!optimisticBase) {
          return
        }
        const base = optimisticBase
        setNodes((current) => rollbackUpdate(current, base))
      },
    }
  }

  function safeSetStatus(message: string) {
    setStatus(message)
  }

  function selectedNodeInfo(currentNodes: CanvasNode[]): { index: number; node: CanvasNode } | undefined {
    const index = currentNodes.findIndex((node) => node.uri === selectedNodeUri)
    if (index < 0) {
      return undefined
    }
    return { index, node: currentNodes[index] }
  }

  async function connectNodes(targetCanvasId = canvasId) {
    const client = clientRef.current
    if (!client || nodes.length < 2) {
      return
    }
    let nextDocument: CanvasDocumentState = { nodes, edges: [] }
    for (let index = 1; index < nodes.length; index += 1) {
      const sourceUri = canvasUri(nodes[index - 1].uri, targetCanvasId)
      const targetUri = canvasUri(nodes[index].uri, targetCanvasId)
      const targetParamId = nodes[index].params[0]?.paramId ?? 'p1'
      await connectCanvasNodes(client, {
        sourceUri,
        targetUri,
        targetParamId,
      })
      nextDocument = upsertCanvasEdge(nextDocument, {
        sourceUri,
        targetUri,
        targetParamId,
      })
      await refreshSubscriptionForUri(targetUri)
    }
    setEdges(nextDocument.edges)
    safeSetStatus(
      `Connected ${nextDocument.edges.length} edge(s) across ${nodes.length} node(s) (${targetCanvasId})`,
    )
  }

  async function disconnectNodes(targetCanvasId = canvasId) {
    const client = clientRef.current
    if (!client || nodes.length < 2) {
      return
    }
    for (let index = 1; index < nodes.length; index += 1) {
      const targetUri = canvasUri(nodes[index].uri, targetCanvasId)
      await disconnectCanvasNodeInput(client, {
        targetUri,
        targetParamId: nodes[index].params[0]?.paramId ?? 'p1',
      })
    }
    setEdges((current) => {
      let next: CanvasDocumentState = { nodes, edges: current }
      for (let index = 1; index < nodes.length; index += 1) {
        next = removeCanvasEdge(
          next,
          canvasUri(nodes[index].uri, targetCanvasId),
          nodes[index].params[0]?.paramId ?? 'p1',
        )
      }
      return next.edges
    })
    try {
      for (let index = 1; index < nodes.length; index += 1) {
        const targetUri = canvasUri(nodes[index].uri, targetCanvasId)
        await refreshSubscriptionForUri(targetUri)
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      safeSetStatus(`Disconnected downstream inputs (${targetCanvasId}); refresh failed: ${message}`)
      return
    }
    safeSetStatus(`Disconnected downstream inputs (${targetCanvasId})`)
  }

  async function renameSelectedParam() {
    const client = clientRef.current
    const selected = selectedNodeInfo(nodes)
    if (!client || !selected || selected.node.params.length === 0) {
      return
    }
    const targetUri = canvasUri(selected.node.uri, canvasId)
    const primary = selected.node.params[0]
    const renamed = `renamed_${Date.now().toString().slice(-3)}`
    const { rollback } = optimisticParamUpdate(
      (current) => {
        const updated = [...current]
        updated[selected.index] = {
          ...updated[selected.index],
          params: updated[selected.index].params.map((param, index) =>
            index === 0 ? { ...param, name: renamed } : param,
          ),
        }
        return updated
      },
      (current) => {
        const updated = [...current]
        updated[selected.index] = {
          ...updated[selected.index],
          params: updated[selected.index].params.map((param) =>
            param.paramId === primary.paramId && param.name === renamed
              ? { ...param, name: primary.name }
              : param,
          ),
        }
        return updated
      },
    )
    try {
      await client.applyPatch(buildPatchForRenameParam(targetUri, primary.paramId, renamed))
      await refreshSubscriptionForUri(targetUri)
      safeSetStatus(`Renamed param ${primary.paramId} -> ${renamed}`)
    } catch (error) {
      rollback()
      throw error
    }
  }

  async function addParam() {
    const client = clientRef.current
    const selected = selectedNodeInfo(nodes)
    if (!client || !selected) {
      return
    }
    const targetUri = canvasUri(selected.node.uri, canvasId)
    const paramId = `p${selected.node.params.length + 1}`
    const name = newParamName.trim() || `param_${paramId}`
    const { rollback } = optimisticParamUpdate(
      (current) => {
        const updated = [...current]
        const alreadyExists = updated[selected.index].params.some((param) => param.paramId === paramId)
        if (alreadyExists) {
          return updated
        }
        updated[selected.index] = {
          ...updated[selected.index],
          params: [...updated[selected.index].params, { name, paramId, typeName: 'Undefined' }],
        }
        return updated
      },
      (current) => {
        const updated = [...current]
        updated[selected.index] = {
          ...updated[selected.index],
          params: updated[selected.index].params.filter((param) => param.paramId !== paramId),
        }
        return updated
      },
    )
    try {
      await client.applyPatch(buildPatchForAddParam(targetUri, { paramId, name, typeName: 'Undefined' }))
      await refreshSubscriptionForUri(targetUri)
      safeSetStatus(`Added param ${name}@${paramId}`)
    } catch (error) {
      rollback()
      throw error
    }
  }

  async function removeParam() {
    const client = clientRef.current
    const selected = selectedNodeInfo(nodes)
    if (!client || !selected || selected.node.params.length === 0) {
      return
    }
    const targetUri = canvasUri(selected.node.uri, canvasId)
    const removed = selected.node.params[selected.node.params.length - 1]
    const removedParamIndex = selected.node.params.length - 1
    const { rollback } = optimisticParamUpdate(
      (current) => {
        const updated = [...current]
        updated[selected.index] = {
          ...updated[selected.index],
          params: updated[selected.index].params.filter((param) => param.paramId !== removed.paramId),
        }
        return updated
      },
      (current, optimisticBase) => {
        const updated = [...current]
        const alreadyPresent = updated[selected.index].params.some((param) => param.paramId === removed.paramId)
        if (alreadyPresent) {
          return updated
        }
        const baseNode = optimisticBase[selected.index]
        const restoredParam =
          baseNode.params.find((param) => param.paramId === removed.paramId) ?? removed
        const insertIndex = Math.min(Math.max(removedParamIndex, 0), updated[selected.index].params.length)
        const nextParams = [...updated[selected.index].params]
        nextParams.splice(insertIndex, 0, restoredParam)
        updated[selected.index] = {
          ...updated[selected.index],
          params: nextParams,
        }
        return updated
      },
    )
    try {
      await client.applyPatch(buildPatchForRemoveParam(targetUri, removed.paramId))
      await refreshSubscriptionForUri(targetUri)
      safeSetStatus(`Removed param ${removed.paramId}`)
    } catch (error) {
      rollback()
      throw error
    }
  }

  async function addNode() {
    const client = clientRef.current
    if (!client) {
      return
    }
    const index = nodes.length + 1
    const node: CanvasNode = {
      uri: `snaq://canvas-a/node-${index}.sl`,
      source: '0',
      params: [],
    }
    const uri = canvasUri(node.uri, canvasId)
    await client.applyPatch([{ op: 'addNode', uri, source: buildNodeSource({ ...node, uri }), version: 1 }])
    setNodes((current) => addCanvasNode({ nodes: current, edges }, node).nodes)
    setSelectedNodeUri(node.uri)
    setSelectedSourceUri(node.uri)
    safeSetStatus(`Added node ${uri}`)
  }

  async function removeSelectedNode() {
    const client = clientRef.current
    if (!client || !selectedNodeUri) {
      return
    }
    const removeUri = canvasUri(selectedNodeUri, canvasId)
    await client.applyPatch([{ op: 'removeNode', uri: removeUri }])
    const existing = nodeSubscriptionsRef.current[removeUri]
    if (existing) {
      await client.unsubscribeNode(existing.subscriptionId)
      setNodeSubscriptionsByUri((current) => {
        const removed = removeNodeSubscriptionByUri(
          { byUri: current, uriById: subscriptionUriByIdRef.current },
          removeUri,
        )
        subscriptionUriByIdRef.current = removed.uriById
        nodeSubscriptionsRef.current = removed.byUri
        return removed.byUri
      })
    }
    const withoutTemplateEdges = removeCanvasNode({ nodes, edges }, selectedNodeUri)
    const next = removeCanvasNode(withoutTemplateEdges, removeUri)
    setNodes(next.nodes)
    setEdges(next.edges)
    safeSetStatus(`Removed node ${removeUri}`)
  }

  async function connectSelectedEdge() {
    const client = clientRef.current
    if (!client || !selectedSourceUri || !selectedTargetUri || !selectedTargetParamId) {
      return
    }
    const sourceUri = canvasUri(selectedSourceUri, canvasId)
    const targetUri = canvasUri(selectedTargetUri, canvasId)
    await connectCanvasNodes(client, {
      sourceUri,
      targetUri,
      targetParamId: selectedTargetParamId,
    })
    setEdges((current) =>
      upsertCanvasEdge(
        {
          nodes,
          edges: current,
        },
        { sourceUri, targetUri, targetParamId: selectedTargetParamId },
      ).edges,
    )
    await refreshSubscriptionForUri(targetUri)
    safeSetStatus(`Connected ${sourceUri} -> ${targetUri}@${selectedTargetParamId}`)
  }

  async function disconnectSelectedEdge() {
    const client = clientRef.current
    if (!client || !selectedTargetUri || !selectedTargetParamId) {
      return
    }
    const targetUri = canvasUri(selectedTargetUri, canvasId)
    try {
      await disconnectCanvasNodeInput(client, {
        targetUri,
        targetParamId: selectedTargetParamId,
      })
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      if (!message.includes('unbound stream input')) {
        throw error
      }
    }
    setEdges((current) =>
      removeCanvasEdge(
        {
          nodes,
          edges: current,
        },
        targetUri,
        selectedTargetParamId,
      ).edges,
    )
    try {
      await refreshSubscriptionForUri(targetUri)
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      safeSetStatus(`Disconnected ${targetUri}@${selectedTargetParamId}; refresh failed: ${message}`)
      return
    }
    safeSetStatus(`Disconnected ${targetUri}@${selectedTargetParamId}`)
  }

  async function unsubscribeAllNodes() {
    const client = clientRef.current
    if (!client) {
      return
    }
    const subscriptions = Object.values(nodeSubscriptionsRef.current)
    for (const subscription of subscriptions) {
      await client.unsubscribeNode(subscription.subscriptionId)
      delete subscriptionUriByIdRef.current[subscription.subscriptionId]
    }
    nodeSubscriptionsRef.current = {}
    setNodeSubscriptionsByUri({})
  }

  async function refreshSubscriptionForUri(uri: string): Promise<void> {
    const client = clientRef.current
    if (!client) {
      return
    }
    const existing = nodeSubscriptionsRef.current[uri]
    if (!existing) {
      return
    }
    await client.unsubscribeNode(existing.subscriptionId)
    const removed = removeNodeSubscriptionByUri(
      { byUri: nodeSubscriptionsRef.current, uriById: subscriptionUriByIdRef.current },
      uri,
    )
    subscriptionUriByIdRef.current = removed.uriById
    nodeSubscriptionsRef.current = removed.byUri
    const response = await client.subscribeNode(uri)
    setNodeSubscriptionsByUri((current) => {
      const merged = registerNodeSubscription(
        { byUri: current, uriById: subscriptionUriByIdRef.current },
        uri,
        {
          subscriptionId: response.subscriptionId,
          resultHandle: response.resultHandle,
        },
      )
      subscriptionUriByIdRef.current = merged.uriById
      nodeSubscriptionsRef.current = merged.byUri
      return upsertNodeSubscription(merged.byUri, uri, {
        subscriptionId: response.subscriptionId,
        resultHandle: response.resultHandle,
      })
    })
  }

  async function subscribeVisibleNodes(targetCanvasId = canvasId): Promise<string | undefined> {
    const client = clientRef.current
    if (!client || nodes.length === 0) {
      return undefined
    }
    let latestHandle: string | undefined
    for (const node of nodes) {
      const sourceUri = canvasUri(node.uri, targetCanvasId)
      const existing = nodeSubscriptionsRef.current[sourceUri]
      if (existing) {
        await client.unsubscribeNode(existing.subscriptionId)
        const removed = removeNodeSubscriptionByUri(
          { byUri: nodeSubscriptionsRef.current, uriById: subscriptionUriByIdRef.current },
          sourceUri,
        )
        subscriptionUriByIdRef.current = removed.uriById
        nodeSubscriptionsRef.current = removed.byUri
      }
      const response = await client.subscribeNode(sourceUri)
      setNodeSubscriptionsByUri((current) => {
        const merged = registerNodeSubscription(
          { byUri: current, uriById: subscriptionUriByIdRef.current },
          sourceUri,
          {
            subscriptionId: response.subscriptionId,
            resultHandle: response.resultHandle,
          },
        )
        subscriptionUriByIdRef.current = merged.uriById
        nodeSubscriptionsRef.current = merged.byUri
        return upsertNodeSubscription(merged.byUri, sourceUri, {
          subscriptionId: response.subscriptionId,
          resultHandle: response.resultHandle,
        })
      })
      latestHandle = response.resultHandle
    }
    setResultHandle(latestHandle)
    paginationRef.current = { offset: 0 }
    if (latestHandle) {
      paginationByHandlePathRef.current[cursorKey(latestHandle)] = { offset: 0 }
    }
    safeSetStatus(`Subscribed to ${nodes.length} node(s) (${targetCanvasId})`)
    return latestHandle
  }

  async function loadFirstSlice(handleOverride?: string) {
    const client = clientRef.current
    const activeResultHandle = handleOverride ?? resultHandle
    if (!client || !activeResultHandle) {
      return
    }
    try {
      const page = await fetchFirstPage(client, { resultHandle: activeResultHandle, limit: 2 })
      paginationRef.current = page.cursor
      paginationByHandlePathRef.current[cursorKey(activeResultHandle)] = page.cursor
      setSlice(JSON.stringify(page.response.elements))
      setStatus('Fetched first page')
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      safeSetStatus(`First slice unavailable: ${message}`)
    }
  }

  async function loadNextSlice(handleOverride?: string) {
    const client = clientRef.current
    const activeResultHandle = handleOverride ?? resultHandle
    if (!client || !activeResultHandle) {
      return
    }
    try {
      const currentCursor =
        paginationByHandlePathRef.current[cursorKey(activeResultHandle)] ?? paginationRef.current
      const page = await fetchNextPage(client, {
        resultHandle: activeResultHandle,
        limit: 2,
        cursor: currentCursor,
      })
      paginationRef.current = page.cursor
      paginationByHandlePathRef.current[cursorKey(activeResultHandle)] = page.cursor
      setSlice(JSON.stringify(page.response.elements))
      setStatus('Fetched next page')
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      safeSetStatus(`Next slice unavailable: ${message}`)
    }
  }

  async function switchCanvas(targetCanvasId = canvasId) {
    const client = clientRef.current
    if (!client) {
      return
    }
    await unsubscribeAllNodes()
    await ensureCanvasSession(client, targetCanvasId, {
      canvasId: targetCanvasId,
      nodes: nodes.map((node) => ({
        uri: canvasUri(node.uri, targetCanvasId),
        source: buildNodeSource({
          ...node,
          uri: canvasUri(node.uri, targetCanvasId),
        }),
        version: 1,
      })),
      edges: edges.map((edge) => ({
        sourceUri: canvasUri(edge.sourceUri, targetCanvasId),
        targetUri: canvasUri(edge.targetUri, targetCanvasId),
        targetParamId: edge.targetParamId,
      })),
    })
    setCanvasId(targetCanvasId)
    safeSetStatus(`Switched to ${targetCanvasId}`)
  }

  function scheduleNodeSourceSync(node: CanvasNode, targetCanvasId = canvasId) {
    const existing = syncTimersRef.current[node.uri]
    if (existing) {
      clearTimeout(existing)
    }
    syncTimersRef.current[node.uri] = setTimeout(() => {
      const client = clientRef.current
      if (!client) {
        return
      }
      void patchCanvasNodeSource(client, node, targetCanvasId).catch((error) => {
        const message = error instanceof Error ? error.message : 'unknown error'
        safeSetStatus(`Auto-sync failed: ${message}`)
      })
    }, 250)
  }

  async function runBridgeScenario() {
    try {
      const primaryCanvas = canvasId
      const recoveryCanvas = `${canvasId}-recovered`
      await initClient()
      const client = clientRef.current
      if (!client) {
        throw new Error('LSP client not initialized')
      }
      await switchCanvas(primaryCanvas)
      await openNodesInLsp(primaryCanvas)
      await patchCanvasNodeSource(
        client,
        { ...nodes[0] },
        primaryCanvas,
      )
      await connectNodes(primaryCanvas)
      await subscribeVisibleNodes(primaryCanvas)
      await switchCanvas(recoveryCanvas)
      await openNodesInLsp(recoveryCanvas)
      await patchCanvasNodeSource(
        client,
        { ...nodes[0] },
        recoveryCanvas,
      )
      await connectNodes(recoveryCanvas)
      await subscribeVisibleNodes(recoveryCanvas)
      safeSetStatus(`Bridge scenario completed (${primaryCanvas} -> ${recoveryCanvas})`)
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      safeSetStatus(`Scenario failed: ${message}`)
    }
  }

  async function runAction(action: () => Promise<void>) {
    try {
      await action()
    } catch (error) {
      const message = error instanceof Error ? error.message : 'unknown error'
      safeSetStatus(`Action failed: ${message}`)
    }
  }

  return (
    <main data-testid="home-page" style={{ minHeight: '100vh', padding: 16, fontFamily: 'sans-serif' }}>
      <h1>Canvas LSP Bridge</h1>
      <p data-testid="status-text">{status}</p>
      <label htmlFor="canvas-id-input">
        Canvas ID
        <input
          id="canvas-id-input"
          data-testid="canvas-id-input"
          value={canvasId}
          onChange={(event) => setCanvasId(event.target.value.trim() || 'canvas-a')}
          style={{ marginLeft: 8 }}
        />
      </label>
      <div style={{ marginTop: 12, display: 'flex', gap: 8, flexWrap: 'wrap' }}>
        <button data-testid="init-worker-btn" onClick={() => void runAction(initClient)}>
          Init Worker
        </button>
        <button data-testid="run-scenario-btn" onClick={() => void runAction(runBridgeScenario)}>
          Run Scenario
        </button>
        <button data-testid="connect-nodes-btn" onClick={() => void runAction(connectNodes)}>
          Connect
        </button>
        <button data-testid="disconnect-nodes-btn" onClick={() => void runAction(disconnectNodes)}>
          Disconnect
        </button>
        <button data-testid="rename-param-btn" onClick={() => void runAction(renameSelectedParam)}>
          Rename Param
        </button>
        <button data-testid="add-param-btn" onClick={() => void runAction(addParam)}>
          Add Param
        </button>
        <button data-testid="remove-param-btn" onClick={() => void runAction(removeParam)}>
          Remove Param
        </button>
        <button data-testid="add-node-btn" onClick={() => void runAction(addNode)}>
          Add Node
        </button>
        <button data-testid="remove-node-btn" onClick={() => void runAction(removeSelectedNode)}>
          Remove Selected Node
        </button>
        <button data-testid="connect-selected-btn" onClick={() => void runAction(connectSelectedEdge)}>
          Connect Selected
        </button>
        <button data-testid="disconnect-selected-btn" onClick={() => void runAction(disconnectSelectedEdge)}>
          Disconnect Selected
        </button>
        <button
          data-testid="subscribe-node-btn"
          onClick={() => void runAction(async () => void (await subscribeVisibleNodes()))}
        >
          Subscribe
        </button>
        <button data-testid="fetch-first-slice-btn" onClick={() => void runAction(loadFirstSlice)}>
          Fetch First Slice
        </button>
        <button data-testid="fetch-next-slice-btn" onClick={() => void runAction(loadNextSlice)}>
          Fetch Next Slice
        </button>
      </div>
      <section style={{ marginTop: 12 }}>
        <h2>Edge Controls</h2>
        <label htmlFor="selected-node-select">
          Node
          <select
            id="selected-node-select"
            data-testid="selected-node-select"
            value={selectedNodeUri}
            onChange={(event) => setSelectedNodeUri(event.target.value)}
            style={{ marginLeft: 8, marginRight: 8 }}
          >
            {nodes.map((node) => (
              <option key={node.uri} value={node.uri}>
                {node.uri}
              </option>
            ))}
          </select>
        </label>
        <label htmlFor="edge-source-select">
          Source
          <select
            id="edge-source-select"
            data-testid="edge-source-select"
            value={selectedSourceUri}
            onChange={(event) => setSelectedSourceUri(event.target.value)}
            style={{ marginLeft: 8, marginRight: 8 }}
          >
            {nodes.map((node) => (
              <option key={node.uri} value={node.uri}>
                {node.uri}
              </option>
            ))}
          </select>
        </label>
        <label htmlFor="edge-target-select">
          Target
          <select
            id="edge-target-select"
            data-testid="edge-target-select"
            value={selectedTargetUri}
            onChange={(event) => setSelectedTargetUri(event.target.value)}
            style={{ marginLeft: 8, marginRight: 8 }}
          >
            {nodes.map((node) => (
              <option key={node.uri} value={node.uri}>
                {node.uri}
              </option>
            ))}
          </select>
        </label>
        <label htmlFor="edge-target-param-select">
          Target Param
          <select
            id="edge-target-param-select"
            data-testid="edge-target-param-select"
            value={selectedTargetParamId}
            onChange={(event) => setSelectedTargetParamId(event.target.value)}
            style={{ marginLeft: 8, marginRight: 8 }}
          >
            {(nodes.find((node) => node.uri === selectedTargetUri)?.params ?? []).map((param) => (
              <option key={param.paramId} value={param.paramId}>
                {param.name}@{param.paramId}
              </option>
            ))}
          </select>
        </label>
      </section>
      <section style={{ marginTop: 16 }}>
        <h2>Node Sources</h2>
        <label htmlFor="new-param-name-input">
          New param name
          <input
            id="new-param-name-input"
            data-testid="new-param-name-input"
            value={newParamName}
            onChange={(event) => setNewParamName(event.target.value)}
            style={{ marginLeft: 8 }}
          />
        </label>
        {nodes.map((node, index) => (
          <label key={node.uri} style={{ display: 'block', marginBottom: 8 }}>
            Node {index + 1} source
            <textarea
              data-testid={`node-source-${index + 1}`}
              value={node.source}
              onChange={(event) => {
                const source = event.target.value
                setNodes((current) => {
                  const nextNodes = current.map((item) =>
                    item.uri === node.uri ? { ...item, source } : item,
                  )
                  const changedNode = nextNodes.find((item) => item.uri === node.uri)
                  if (changedNode) {
                    scheduleNodeSourceSync(changedNode)
                  }
                  return nextNodes
                })
              }}
              style={{ display: 'block', width: 480, height: 72 }}
            />
          </label>
        ))}
        <div data-testid="param-summary">
          {(nodes.find((node) => node.uri === selectedNodeUri)?.params ?? [])
            .map((param) => `${param.name}@${param.paramId}:${param.typeName}`)
            .join(', ')}
        </div>
      </section>
      <section style={{ marginTop: 16 }}>
        <div data-testid="subscription-id">
          Subscription:{' '}
          {Object.values(nodeSubscriptionsByUri)
            .map((entry) => entry.subscriptionId)
            .join(', ') || 'none'}
        </div>
        <div data-testid="result-handle">Result handle: {resultHandle ?? 'none'}</div>
        <div data-testid="slice-output">Slice: {slice}</div>
      </section>
      <section style={{ marginTop: 16 }}>
        <h2>Node Result Status</h2>
        <ul data-testid="node-result-status">
          {Object.entries(nodeResultsByUri).map(([uri, result]) => (
            <li key={uri}>
              {uri}: {result.status}
            </li>
          ))}
        </ul>
      </section>
      <section style={{ marginTop: 16 }}>
        <h2>Notification Log</h2>
        <ul data-testid="notification-log">
          {notifications.map((entry, index) => (
            <li key={`${entry}-${index}`}>{entry}</li>
          ))}
        </ul>
      </section>
    </main>
  )
}
