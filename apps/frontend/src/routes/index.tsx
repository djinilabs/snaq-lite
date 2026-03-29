import { createFileRoute } from '@tanstack/react-router'
import { useMemo, useRef, useState } from 'react'
import { createLspClient, type LspClient } from '../lsp/client'
import LspWorker from '../lsp/lsp.worker?worker'
import {
  buildPatchForAddParam,
  buildNodeSource,
  buildPatchForConnect,
  buildPatchForDisconnect,
  buildPatchForRemoveParam,
  buildPatchForRenameParam,
  type CanvasNode,
} from '../lsp/graph-patch'
import { fetchFirstPage, fetchNextPage, type PageCursor } from '../lsp/pagination'
import { ensureCanvasSession } from '../lsp/session-orchestrator'

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
  ])
  const [subscriptionId, setSubscriptionId] = useState<string>()
  const [resultHandle, setResultHandle] = useState<string>()
  const [slice, setSlice] = useState<string>('[]')
  const [newParamName, setNewParamName] = useState('x2')
  const paginationRef = useRef<PageCursor>({ offset: 0 })
  const clientRef = useRef<LspClient | null>(null)
  const wasmUrl = useMemo(() => {
    if (typeof window === 'undefined') {
      return '/lsp-wasm/snaq_lite_lsp.js'
    }
    return `${window.location.origin}${import.meta.env.BASE_URL}lsp-wasm/snaq_lite_lsp.js`
  }, [])

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
    for (const node of nodes) {
      const uri = node.uri.replace(/snaq:\/\/[^/]+\//, `snaq://${targetCanvasId}/`)
      await client.sendNotification('textDocument/didOpen', {
        textDocument: {
          uri,
          languageId: 'snaq',
          version: 1,
          text: buildNodeSource({ ...node, uri }),
        },
      })
    }
  }

  function canvasUri(uri: string, targetCanvasId: string): string {
    return uri.replace(/snaq:\/\/[^/]+\//, `snaq://${targetCanvasId}/`)
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
    const sourceUri = canvasUri(nodes[0].uri, targetCanvasId)
    const targetUri = canvasUri(nodes[1].uri, targetCanvasId)
    const operation = buildPatchForConnect({
      sourceUri,
      targetUri,
      targetParamId: nodes[1].params[0]?.paramId ?? 'p1',
    })[0]
    await client.applyPatch([operation])
    safeSetStatus(`Connected node-1 -> node-2 (${targetCanvasId})`)
  }

  async function disconnectNodes(targetCanvasId = canvasId) {
    const client = clientRef.current
    if (!client || nodes.length < 2) {
      return
    }
    const targetUri = canvasUri(nodes[1].uri, targetCanvasId)
    const operation = buildPatchForDisconnect({
      sourceUri: '',
      targetUri,
      targetParamId: nodes[1].params[0]?.paramId ?? 'p1',
    })[0]
    await client.applyPatch([operation])
    safeSetStatus(`Disconnected node-2 input (${targetCanvasId})`)
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
      safeSetStatus(`Removed param ${removed.paramId}`)
    } catch (error) {
      rollback()
      throw error
    }
  }

  async function subscribeSecondNode(targetCanvasId = canvasId): Promise<string | undefined> {
    const client = clientRef.current
    if (!client || nodes.length < 2) {
      return undefined
    }
    const sourceUri = canvasUri(nodes[1].uri, targetCanvasId)
    const response = await client.sendRequest<{ subscriptionId: string; resultHandle?: string }>(
      'snaqlite/subscribeNode',
      { sourceUri },
    )
    setSubscriptionId(response.subscriptionId)
    setResultHandle(response.resultHandle)
    paginationRef.current = { offset: 0 }
    safeSetStatus(`Subscribed to node-2 (${targetCanvasId})`)
    return response.resultHandle
  }

  async function loadFirstSlice(handleOverride?: string) {
    const client = clientRef.current
    const activeResultHandle = handleOverride ?? resultHandle
    if (!client || !activeResultHandle) {
      return
    }
    const page = await fetchFirstPage(client, { resultHandle: activeResultHandle, limit: 2 })
    paginationRef.current = page.cursor
    setSlice(JSON.stringify(page.response.elements))
    setStatus('Fetched first page')
  }

  async function loadNextSlice(handleOverride?: string) {
    const client = clientRef.current
    const activeResultHandle = handleOverride ?? resultHandle
    if (!client || !activeResultHandle) {
      return
    }
    const page = await fetchNextPage(client, {
      resultHandle: activeResultHandle,
      limit: 2,
      cursor: paginationRef.current,
    })
    paginationRef.current = page.cursor
    setSlice(JSON.stringify(page.response.elements))
    setStatus('Fetched next page')
  }

  async function switchCanvas(targetCanvasId = canvasId) {
    const client = clientRef.current
    if (!client) {
      return
    }
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
      edges: [],
    })
    safeSetStatus(`Switched to ${targetCanvasId}`)
  }

  async function runBridgeScenario() {
    try {
      const primaryCanvas = canvasId
      const recoveryCanvas = `${canvasId}-recovered`
      await initClient()
      await switchCanvas(primaryCanvas)
      await openNodesInLsp(primaryCanvas)
      await connectNodes(primaryCanvas)
      const primaryResultHandle = await subscribeSecondNode(primaryCanvas)
      await loadFirstSlice(primaryResultHandle)
      await switchCanvas(recoveryCanvas)
      await openNodesInLsp(recoveryCanvas)
      await connectNodes(recoveryCanvas)
      const recoveryResultHandle = await subscribeSecondNode(recoveryCanvas)
      await loadNextSlice(recoveryResultHandle)
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
          onClick={() => void runAction(async () => void (await subscribeSecondNode()))}
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
                setNodes((current) =>
                  current.map((item) => (item.uri === node.uri ? { ...item, source } : item)),
                )
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
        <div data-testid="subscription-id">Subscription: {subscriptionId ?? 'none'}</div>
        <div data-testid="result-handle">Result handle: {resultHandle ?? 'none'}</div>
        <div data-testid="slice-output">Slice: {slice}</div>
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
