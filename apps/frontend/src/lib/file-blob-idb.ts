/**
 * IndexedDB persistence for file block blobs. Keyed by (projectId, nodeId) so
 * dropped files survive reload. Open DB on first use; one object store, key = projectId + "|" + nodeId.
 */

const DB_NAME = 'snaq-file-blobs'
const DB_VERSION = 1
const STORE_NAME = 'blobs'

const KEY_SEP = '|'

function key(projectId: string, nodeId: string): string {
  return projectId + KEY_SEP + nodeId
}

let dbOpen: Promise<IDBDatabase> | null = null

function openDb(): Promise<IDBDatabase> {
  if (dbOpen) return dbOpen
  dbOpen = new Promise((resolve, reject) => {
    if (typeof indexedDB === 'undefined') {
      reject(new Error('IndexedDB not available'))
      return
    }
    const req = indexedDB.open(DB_NAME, DB_VERSION)
    req.onerror = () => reject(req.error)
    req.onsuccess = () => resolve(req.result)
    req.onupgradeneeded = (e) => {
      const db = (e.target as IDBOpenDBRequest).result
      if (!db.objectStoreNames.contains(STORE_NAME)) {
        db.createObjectStore(STORE_NAME)
      }
    }
  })
  return dbOpen
}

/**
 * Store a file blob for a file node. Overwrites if present.
 */
export function putFileBlob(projectId: string, nodeId: string, blob: Blob): Promise<void> {
  return openDb().then(
    (db) =>
      new Promise((resolve, reject) => {
        const tx = db.transaction(STORE_NAME, 'readwrite')
        const store = tx.objectStore(STORE_NAME)
        const req = store.put(blob, key(projectId, nodeId))
        req.onsuccess = () => resolve()
        req.onerror = () => reject(req.error)
      }),
  )
}

/**
 * Retrieve a file blob, or null if not found.
 */
export function getFileBlob(projectId: string, nodeId: string): Promise<Blob | null> {
  return openDb().then(
    (db) =>
      new Promise((resolve, reject) => {
        const tx = db.transaction(STORE_NAME, 'readonly')
        const store = tx.objectStore(STORE_NAME)
        const req = store.get(key(projectId, nodeId))
        req.onsuccess = () => resolve(req.result ?? null)
        req.onerror = () => reject(req.error)
      }),
  )
}

/**
 * Remove the blob for one file node.
 */
export function deleteFileBlob(projectId: string, nodeId: string): Promise<void> {
  return openDb().then(
    (db) =>
      new Promise((resolve, reject) => {
        const tx = db.transaction(STORE_NAME, 'readwrite')
        const store = tx.objectStore(STORE_NAME)
        const req = store.delete(key(projectId, nodeId))
        req.onsuccess = () => resolve()
        req.onerror = () => reject(req.error)
      }),
  )
}

/**
 * Remove all blobs for a project (e.g. when deleting the project).
 * Uses IDBKeyRange to iterate keys with prefix projectId + KEY_SEP.
 */
export function deleteAllBlobsForProject(projectId: string): Promise<void> {
  const prefix = projectId + KEY_SEP
  const range = IDBKeyRange.bound(prefix, prefix + '\uffff', false, false)

  return openDb().then(
    (db) =>
      new Promise((resolve, reject) => {
        const tx = db.transaction(STORE_NAME, 'readwrite')
        const store = tx.objectStore(STORE_NAME)
        tx.oncomplete = () => resolve()
        tx.onerror = () => reject(tx.error)
        const req = store.openCursor(range)
        req.onsuccess = () => {
          const cursor = req.result
          if (cursor) {
            cursor.delete()
            cursor.continue()
          }
        }
        req.onerror = () => reject(req.error)
      }),
  )
}
