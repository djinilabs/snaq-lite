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

  function pathKey(resultHandleValue: string, path: Array<number | string> = []): string {
    return `${resultHandleValue}:${JSON.stringify(path)}`
  }

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

  async function connectNodes(targetCanvasId = canvasId) {
    const client = clientRef.current
    if (!client || nodes.length < 2) {
      return
    }
    const nextEdges: CanvasEdge[] = []
    for (let index = 1; index < nodes.length; index += 1) {
      const sourceUri = canvasUri(nodes[index - 1].uri, targetCanvasId)
      const targetUri = canvasUri(nodes[index].uri, targetCanvasId)
      const targetParamId = nodes[index].params[0]?.paramId ?? 'p1'
      await connectCanvasNodes(client, {
        sourceUri,
        targetUri,
        targetParamId,
      })
      nextEdges.push({
        sourceUri,
        targetUri,
        targetParamId,
      })
      await refreshSubscriptionForUri(targetUri)
    }
    setEdges(nextEdges)
    safeSetStatus(`Connected ${nextEdges.length} edge(s) across ${nodes.length} node(s) (${targetCanvasId})`)
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
    setEdges([])
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

  async function renamePrimaryParam() {
    const client = clientRef.current
    if (!client || nodes.length < 2 || nodes[1].params.length === 0) {
      return
    }
    const targetUri = canvasUri(nodes[1].uri, canvasId)
    const primary = nodes[1].params[0]
    const renamed = `renamed_${Date.now().toString().slice(-3)}`
    const { rollback } = optimisticParamUpdate(
      (current) => {
        const updated = [...current]
        updated[1] = {
          ...updated[1],
          params: updated[1].params.map((param, index) =>
            index === 0 ? { ...param, name: renamed } : param,
          ),
        }
        return updated
      },
      (current) => {
        const updated = [...current]
        updated[1] = {
          ...updated[1],
          params: updated[1].params.map((param) =>
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
    if (!client || nodes.length < 2) {
      return
    }
    const targetUri = canvasUri(nodes[1].uri, canvasId)
    const paramId = `p${nodes[1].params.length + 1}`
    const name = newParamName.trim() || `param_${paramId}`
    const { rollback } = optimisticParamUpdate(
      (current) => {
        const updated = [...current]
        const alreadyExists = updated[1].params.some((param) => param.paramId === paramId)
        if (alreadyExists) {
          return updated
        }
        updated[1] = {
          ...updated[1],
          params: [...updated[1].params, { name, paramId, typeName: 'Undefined' }],
        }
        return updated
      },
      (current) => {
        const updated = [...current]
        updated[1] = {
          ...updated[1],
          params: updated[1].params.filter((param) => param.paramId !== paramId),
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
    if (!client || nodes.length < 2 || nodes[1].params.length === 0) {
      return
    }
    const targetUri = canvasUri(nodes[1].uri, canvasId)
    const removed = nodes[1].params[nodes[1].params.length - 1]
    const removedParamIndex = nodes[1].params.length - 1
    const { rollback } = optimisticParamUpdate(
      (current) => {
        const updated = [...current]
        updated[1] = {
          ...updated[1],
          params: updated[1].params.filter((param) => param.paramId !== removed.paramId),
        }
        return updated
      },
      (current, optimisticBase) => {
        const updated = [...current]
        const alreadyPresent = updated[1].params.some((param) => param.paramId === removed.paramId)
        if (alreadyPresent) {
          return updated
        }
        const baseNode = optimisticBase[1]
        const restoredParam =
          baseNode.params.find((param) => param.paramId === removed.paramId) ?? removed
        const insertIndex = Math.min(Math.max(removedParamIndex, 0), updated[1].params.length)
        const nextParams = [...updated[1].params]
        nextParams.splice(insertIndex, 0, restoredParam)
        updated[1] = {
          ...updated[1],
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
    delete subscriptionUriByIdRef.current[existing.subscriptionId]
    const response = await client.subscribeNode(uri)
    subscriptionUriByIdRef.current[response.subscriptionId] = uri
    setNodeSubscriptionsByUri((current) =>
      upsertNodeSubscription(current, uri, {
        subscriptionId: response.subscriptionId,
        resultHandle: response.resultHandle,
      }),
    )
  }

  async function subscribeDownstreamNodes(targetCanvasId = canvasId): Promise<string | undefined> {
    const client = clientRef.current
    if (!client || nodes.length < 2) {
      return undefined
    }
    let latestHandle: string | undefined
    for (let index = 1; index < nodes.length; index += 1) {
      const sourceUri = canvasUri(nodes[index].uri, targetCanvasId)
      const existing = nodeSubscriptionsRef.current[sourceUri]
      if (existing) {
        await client.unsubscribeNode(existing.subscriptionId)
        delete subscriptionUriByIdRef.current[existing.subscriptionId]
      }
      const response = await client.subscribeNode(sourceUri)
      subscriptionUriByIdRef.current[response.subscriptionId] = sourceUri
      setNodeSubscriptionsByUri((current) =>
        upsertNodeSubscription(current, sourceUri, {
          subscriptionId: response.subscriptionId,
          resultHandle: response.resultHandle,
        }),
      )
      latestHandle = response.resultHandle
    }
    setResultHandle(latestHandle)
    paginationRef.current = { offset: 0 }
    if (latestHandle) {
      paginationByHandlePathRef.current[pathKey(latestHandle)] = { offset: 0 }
    }
    safeSetStatus(`Subscribed to ${Math.max(nodes.length - 1, 0)} downstream node(s) (${targetCanvasId})`)
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
      paginationByHandlePathRef.current[pathKey(activeResultHandle)] = page.cursor
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
        paginationByHandlePathRef.current[pathKey(activeResultHandle)] ?? paginationRef.current
      const page = await fetchNextPage(client, {
        resultHandle: activeResultHandle,
        limit: 2,
        cursor: currentCursor,
      })
      paginationRef.current = page.cursor
      paginationByHandlePathRef.current[pathKey(activeResultHandle)] = page.cursor
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
      await subscribeDownstreamNodes(primaryCanvas)
      await switchCanvas(recoveryCanvas)
      await openNodesInLsp(recoveryCanvas)
      await patchCanvasNodeSource(
        client,
        { ...nodes[0] },
        recoveryCanvas,
      )
      await connectNodes(recoveryCanvas)
      await subscribeDownstreamNodes(recoveryCanvas)
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
        <button data-testid="rename-param-btn" onClick={() => void runAction(renamePrimaryParam)}>
          Rename Param
        </button>
        <button data-testid="add-param-btn" onClick={() => void runAction(addParam)}>
          Add Param
        </button>
        <button data-testid="remove-param-btn" onClick={() => void runAction(removeParam)}>
          Remove Param
        </button>
        <button
          data-testid="subscribe-node-btn"
          onClick={() => void runAction(async () => void (await subscribeDownstreamNodes()))}
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
          {nodes[1].params.map((param) => `${param.name}@${param.paramId}:${param.typeName}`).join(', ')}
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
