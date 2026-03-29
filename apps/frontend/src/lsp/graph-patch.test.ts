import { describe, expect, it } from 'vitest'
import {
  buildNodeSource,
  buildPatchForAddParam,
  buildPatchForConnect,
  buildPatchForDisconnect,
  buildPatchForNodeEdit,
  buildPatchForRemoveParam,
  buildPatchForRenameParam,
} from './graph-patch'

describe('graph patch helpers', () => {
  it('builds deterministic source with param ids', () => {
    const source = buildNodeSource({
      uri: 'snaq://canvas-a/node-1.sl',
      source: 'x * 2',
      params: [{ name: 'x', paramId: 'p1', typeName: 'Numeric' }],
    })
    expect(source).toBe('input x@p1: Numeric\nx * 2')
  })

  it('creates setNodeSource patch for node edits', () => {
    const patch = buildPatchForNodeEdit({
      uri: 'snaq://canvas-a/node-2.sl',
      source: '$x',
      params: [{ name: 'x', paramId: 'p1', typeName: 'Vector' }],
    })
    expect(patch[0]).toEqual({
      op: 'setNodeSource',
      uri: 'snaq://canvas-a/node-2.sl',
      source: 'input x@p1: Vector\n$x',
    })
  })

  it('creates connect and disconnect operations keyed by paramId', () => {
    const connect = buildPatchForConnect({
      sourceUri: 'snaq://canvas-a/a.sl',
      targetUri: 'snaq://canvas-a/b.sl',
      targetParamId: 'p1',
    })
    const disconnect = buildPatchForDisconnect({
      sourceUri: 'snaq://canvas-a/a.sl',
      targetUri: 'snaq://canvas-a/b.sl',
      targetParamId: 'p1',
    })
    expect(connect[0]).toMatchObject({ op: 'connect', targetInputName: 'p1' })
    expect(disconnect[0]).toMatchObject({ op: 'disconnect', targetInputName: 'p1' })
  })

  it('creates rename/add/remove param operations keyed by paramId', () => {
    const rename = buildPatchForRenameParam('snaq://canvas-a/node-2.sl', 'p1', 'renamed')
    const add = buildPatchForAddParam('snaq://canvas-a/node-2.sl', {
      paramId: 'p2',
      name: 'newParam',
      typeName: 'Numeric',
    })
    const remove = buildPatchForRemoveParam('snaq://canvas-a/node-2.sl', 'p2')
    expect(rename[0]).toEqual({
      op: 'renameParam',
      uri: 'snaq://canvas-a/node-2.sl',
      paramId: 'p1',
      newName: 'renamed',
    })
    expect(add[0]).toEqual({
      op: 'addParam',
      uri: 'snaq://canvas-a/node-2.sl',
      paramId: 'p2',
      name: 'newParam',
      typeName: 'Numeric',
    })
    expect(remove[0]).toEqual({
      op: 'removeParam',
      uri: 'snaq://canvas-a/node-2.sl',
      paramId: 'p2',
    })
  })
})
