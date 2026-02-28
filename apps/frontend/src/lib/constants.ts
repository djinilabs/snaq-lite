/** Virtual document URI prefix for graph nodes (matches LSP and docs). */
export const VIRTUAL_URI_PREFIX = 'snaq://graph/'

/** Worker control message types (init from main, ready/error from worker). */
export const WORKER_MSG_INIT = 'init'
export const WORKER_MSG_READY = 'snaqlite-worker-ready'
export const WORKER_MSG_ERROR = 'snaqlite-worker-error'

export const LSP_METHOD_GRAPH_CONNECT = 'snaqlite/graph/connect'
export const LSP_METHOD_GRAPH_DISCONNECT = 'snaqlite/graph/disconnect'
export const LSP_METHOD_SUBSCRIBE_WIDGET = 'snaqlite/graph/subscribeWidget'
export const LSP_METHOD_UNSUBSCRIBE_WIDGET = 'snaqlite/graph/unsubscribeWidget'
