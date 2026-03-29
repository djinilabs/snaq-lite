import type { LspClient } from './client'
import {
  buildNodeSource,
  buildPatchForConnect,
  buildPatchForDisconnect,
  buildPatchForNodeEdit,
  type CanvasNode,
} from './graph-patch'

export function toCanvasUri(uri: string, canvasId: string): string {
  const parsed = new URL(uri)
  if (parsed.protocol !== 'snaq:') {
    throw new Error(`Expected snaq:// URI, got ${uri}`)
  }
  if (!parsed.hostname) {
    throw new Error(`Expected canvas host in URI, got ${uri}`)
  }
  if (!canvasId.trim()) {
    throw new Error('canvasId must not be empty')
  }
  parsed.hostname = canvasId
  return parsed.toString()
}

export async function openCanvasNodes(
  client: LspClient,
  nodes: CanvasNode[],
  canvasId: string,
): Promise<void> {
  for (const node of nodes) {
    const uri = toCanvasUri(node.uri, canvasId)
    await client.didOpen({
      uri,
      text: buildNodeSource({ ...node, uri }),
      version: 1,
    })
  }
}

export async function patchCanvasNodeSource(
  client: LspClient,
  node: CanvasNode,
  canvasId: string,
): Promise<void> {
  const uri = toCanvasUri(node.uri, canvasId)
  await client.applyPatch(
    buildPatchForNodeEdit({
      ...node,
      uri,
    }),
  )
}

export async function connectCanvasNodes(
  client: LspClient,
  params: { sourceUri: string; targetUri: string; targetParamId: string },
): Promise<void> {
  await client.applyPatch(
    buildPatchForConnect({
      sourceUri: params.sourceUri,
      targetUri: params.targetUri,
      targetParamId: params.targetParamId,
    }),
  )
}

export async function disconnectCanvasNodeInput(
  client: LspClient,
  params: { targetUri: string; targetParamId: string },
): Promise<void> {
  await client.applyPatch(
    buildPatchForDisconnect({
      sourceUri: '',
      targetUri: params.targetUri,
      targetParamId: params.targetParamId,
    }),
  )
}
