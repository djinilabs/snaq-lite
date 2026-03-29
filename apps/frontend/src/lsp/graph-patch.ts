import type { GraphPatchOperation } from './types'

export type CanvasParam = {
  name: string
  paramId: string
  typeName: string
}

export type CanvasNode = {
  uri: string
  source: string
  params: CanvasParam[]
}

export type CanvasEdge = {
  sourceUri: string
  targetUri: string
  targetParamId: string
}

export function buildNodeSource(node: CanvasNode): string {
  const header = node.params
    .map((param) => `input ${param.name}@${param.paramId}: ${param.typeName}`)
    .join('\n')
  if (!header) {
    return node.source
  }
  return `${header}\n${node.source}`
}

export function buildPatchForNodeEdit(node: CanvasNode): GraphPatchOperation[] {
  return [{ op: 'setNodeSource', uri: node.uri, source: buildNodeSource(node) }]
}

export function buildPatchForConnect(edge: CanvasEdge): GraphPatchOperation[] {
  return [
    {
      op: 'connect',
      sourceUri: edge.sourceUri,
      targetUri: edge.targetUri,
      targetInputName: edge.targetParamId,
    },
  ]
}

export function buildPatchForDisconnect(edge: CanvasEdge): GraphPatchOperation[] {
  return [
    {
      op: 'disconnect',
      targetUri: edge.targetUri,
      targetInputName: edge.targetParamId,
    },
  ]
}

export function buildPatchForRenameParam(uri: string, paramId: string, newName: string): GraphPatchOperation[] {
  return [{ op: 'renameParam', uri, paramId, newName }]
}

export function buildPatchForAddParam(
  uri: string,
  param: { paramId: string; name: string; typeName: string },
): GraphPatchOperation[] {
  return [{ op: 'addParam', uri, paramId: param.paramId, name: param.name, typeName: param.typeName }]
}

export function buildPatchForRemoveParam(uri: string, paramId: string): GraphPatchOperation[] {
  return [{ op: 'removeParam', uri, paramId }]
}

export function invertOperations(operations: GraphPatchOperation[]): GraphPatchOperation[] {
  const inverted: GraphPatchOperation[] = []
  for (let i = operations.length - 1; i >= 0; i -= 1) {
    const operation = operations[i]
    switch (operation.op) {
      case 'connect':
        inverted.push({
          op: 'disconnect',
          targetUri: operation.targetUri,
          targetInputName: operation.targetInputName,
        })
        break
      case 'addNode':
      case 'removeNode':
      case 'disconnect':
        // Disconnect inversion needs source context; caller should provide explicit rollback for this case.
        break
      case 'setNodeSource':
      case 'renameParam':
      case 'addParam':
      case 'removeParam':
        // Source-mutation inversion also needs prior state; handled by caller.
        break
      default: {
        const _exhaustive: never = operation
        throw new Error(`Unsupported patch operation for inversion: ${JSON.stringify(_exhaustive)}`)
      }
    }
  }
  return inverted
}
