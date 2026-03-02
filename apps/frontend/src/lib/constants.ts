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

/** LSP textDocument/didOpen (shared by computation-box-editor and computation-box-node). */
export const LSP_METHOD_DID_OPEN = 'textDocument/didOpen'
/** LSP textDocument/didChange (used by computation-box-editor). */
export const LSP_METHOD_DID_CHANGE = 'textDocument/didChange'

/** Retry interval and max wait when LSP client is not ready before subscribeWidget. */
export const LSP_SUBSCRIBE_RETRY_INTERVAL_MS = 200
export const LSP_SUBSCRIBE_MAX_WAIT_MS = 10_000
/** Delay after onBeforeSubscribe before sending subscribeWidget so worker processes didOpen first. */
export const LSP_SUBSCRIBE_AFTER_DID_OPEN_MS = 150

/** React Flow drag handle class names; only elements with this class start a node drag. */
export const DRAG_HANDLE_CLASS_COMPUTATION = 'computation-drag-handle'
export const DRAG_HANDLE_CLASS_PRESENTATION = 'presentation-drag-handle'

/** React Flow utility class; elements with this class do not start a node drag (so inner UI is clickable). */
export const NODRAG_CLASS = 'nodrag'

/** Prevents wheel from panning/zooming the canvas when over node content. */
export const NOWHEEL_CLASS = 'nowheel'

/** Allowed types for computation block input ports (use $name in script to reference). */
export const INPUT_PORT_TYPES = ['Vector', 'Numeric', 'Symbolic', 'FuzzyBool', 'Undefined'] as const

/** Debounce delay (ms) before auto-saving after graph or editor content change. */
export const AUTO_SAVE_DEBOUNCE_MS = 600

/** Maximum number of states kept in the undo stack (canvas boxes + connections). */
export const UNDO_STACK_MAX = 10
