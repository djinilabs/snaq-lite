/**
 * Unit tests for file-blob-idb. Uses a fake IndexedDB implementation
 * so tests run in Node where indexedDB is not available.
 */

import { describe, it, expect, beforeAll, beforeEach, vi } from 'vitest'

const STORE_NAME = 'blobs'
const store = new Map<string, Blob>()


function createFakeIdb() {
  const fakeOpenRequest = {
    result: null as IDBDatabase | null,
    onsuccess: null as (() => void) | null,
    onerror: null as (() => void) | null,
    onupgradeneeded: null as ((e: { target: { result: IDBDatabase } }) => void) | null,
  }
  const fakeDb = {
    objectStoreNames: { contains: (name: string) => name === STORE_NAME },
    createObjectStore: () => {},
    transaction: (_mode: string) => {
      const tx = {
        oncomplete: null as (() => void) | null,
        onerror: null as (() => void) | null,
        error: null as unknown,
        objectStore: () => ({
          put: (value: Blob, k: string) => {
            store.set(k, value)
            const putReq = { onsuccess: null as (() => void) | null, onerror: null }
            queueMicrotask(() => putReq.onsuccess?.())
            return putReq
          },
          get: (k: string) => {
            const req = {
              result: undefined as Blob | null | undefined,
              onsuccess: null as (() => void) | null,
              onerror: null,
            }
            queueMicrotask(() => {
              req.result = store.get(k) ?? null
              req.onsuccess?.()
            })
            return req
          },
          delete: (k: string) => {
            store.delete(k)
            const delReq = { onsuccess: null as (() => void) | null, onerror: null }
            queueMicrotask(() => delReq.onsuccess?.())
            return delReq
          },
          openCursor: (range: { lower: string; upper: string } | null) => {
            const keys = range
              ? [...store.keys()].filter((k) => k >= range.lower && k <= range.upper)
              : [...store.keys()]
            let i = 0
            const req = {
              result: null as { key: string; delete: () => void; continue: () => void } | null,
              onsuccess: null as (() => void) | null,
              onerror: null,
            }
            const next = () => {
              if (i < keys.length) {
                req.result = {
                  key: keys[i],
                  delete: () => {
                    store.delete(keys[i])
                  },
                  continue: () => {
                    i++
                    queueMicrotask(next)
                  },
                }
                queueMicrotask(() => req.onsuccess?.())
              } else {
                req.result = null
                queueMicrotask(() => {
                  req.onsuccess?.()
                  tx.oncomplete?.()
                })
              }
            }
            queueMicrotask(next)
            return req
          },
        }),
      }
      return tx
    },
  }
  return {
    open: (_name: string, _version: number) => {
      fakeOpenRequest.result = fakeDb as unknown as IDBDatabase
      queueMicrotask(() => {
        fakeOpenRequest.onupgradeneeded?.({ target: { result: fakeDb as unknown as IDBDatabase } })
        fakeOpenRequest.onsuccess?.()
      })
      return fakeOpenRequest
    },
  }
}

let putFileBlob: (projectId: string, nodeId: string, blob: Blob) => Promise<void>
let getFileBlob: (projectId: string, nodeId: string) => Promise<Blob | null>
let deleteFileBlob: (projectId: string, nodeId: string) => Promise<void>
let deleteAllBlobsForProject: (projectId: string) => Promise<void>

beforeAll(async () => {
  vi.stubGlobal('indexedDB', {
    open: (name: string, version: number) => {
      const fake = createFakeIdb()
      return fake.open(name, version)
    },
  })
  vi.stubGlobal('IDBKeyRange', {
    bound: (lower: string, upper: string) => ({ lower, upper }),
  })
  const mod = await import('./file-blob-idb')
  putFileBlob = mod.putFileBlob
  getFileBlob = mod.getFileBlob
  deleteFileBlob = mod.deleteFileBlob
  deleteAllBlobsForProject = mod.deleteAllBlobsForProject
})

beforeEach(() => {
  store.clear()
})

describe('file-blob-idb', () => {
  it('putFileBlob stores blob and getFileBlob retrieves it', async () => {
    const blob = new Blob(['hello'])
    await putFileBlob('proj1', 'node1', blob)
    const out = await getFileBlob('proj1', 'node1')
    expect(out).not.toBeNull()
    expect(out).toBe(blob)
    expect(out!.size).toBe(5)
  })

  it('getFileBlob returns null when not found', async () => {
    const out = await getFileBlob('proj1', 'node1')
    expect(out).toBeNull()
  })

  it('deleteFileBlob removes the blob', async () => {
    await putFileBlob('p', 'n', new Blob(['x']))
    await deleteFileBlob('p', 'n')
    expect(await getFileBlob('p', 'n')).toBeNull()
  })

  it('deleteAllBlobsForProject removes only blobs for that project', async () => {
    await putFileBlob('proj-a', 'n1', new Blob(['a1']))
    await putFileBlob('proj-a', 'n2', new Blob(['a2']))
    await putFileBlob('proj-b', 'n1', new Blob(['b1']))
    await deleteAllBlobsForProject('proj-a')
    expect(await getFileBlob('proj-a', 'n1')).toBeNull()
    expect(await getFileBlob('proj-a', 'n2')).toBeNull()
    expect(await getFileBlob('proj-b', 'n1')).not.toBeNull()
  })
})
