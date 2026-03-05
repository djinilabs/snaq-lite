/** Virtual document URI prefix for graph nodes (matches LSP and docs). */
export const VIRTUAL_URI_PREFIX = 'snaq://graph/'

/** Worker control message types (init from main, ready/error from worker). */
export const WORKER_MSG_INIT = 'init'
export const WORKER_MSG_READY = 'snaqlite-worker-ready'
export const WORKER_MSG_ERROR = 'snaqlite-worker-error'
/** Worker response for createStreamInput (id + index). */
export const WORKER_MSG_CREATE_STREAM_RESPONSE = 'createStreamInputResponse'

export const LSP_METHOD_GRAPH_CONNECT = 'snaqlite/graph/connect'
export const LSP_METHOD_GRAPH_DISCONNECT = 'snaqlite/graph/disconnect'
export const LSP_METHOD_SUBSCRIBE_WIDGET = 'snaqlite/graph/subscribeWidget'
export const LSP_METHOD_UNSUBSCRIBE_WIDGET = 'snaqlite/graph/unsubscribeWidget'
export const LSP_METHOD_FETCH_RESULT_SLICE = 'snaqlite/graph/fetchResultSlice'

/** LSP textDocument/didOpen (shared by computation-box-editor and computation-box-node). */
export const LSP_METHOD_DID_OPEN = 'textDocument/didOpen'

/** Default document content for presentation nodes so LSP has target document open for graph_connect. Input type Undefined = accept any (no type check); name must match Handle id. */
export const DEFAULT_PRESENTATION_DOCUMENT_CONTENT = 'input x: Undefined\n$x'
/** LSP textDocument/didChange (used by computation-box-editor). */
export const LSP_METHOD_DID_CHANGE = 'textDocument/didChange'

/** Retry interval and max wait when LSP client is not ready before subscribeWidget. */
export const LSP_SUBSCRIBE_RETRY_INTERVAL_MS = 200
export const LSP_SUBSCRIBE_MAX_WAIT_MS = 10_000
/** Timeout for createStreamInput request to the LSP worker (file-block external streams). */
export const CREATE_STREAM_INPUT_TIMEOUT_MS = 10_000
/** Delay after onBeforeSubscribe before sending subscribeWidget so worker processes didOpen first. */
export const LSP_SUBSCRIBE_AFTER_DID_OPEN_MS = 150

/** Default page size for fetchResultSlice (vectors and maps). */
export const RESULT_SLICE_PAGE_SIZE = 50

/** React Flow drag handle class names; only elements with this class start a node drag. */
export const DRAG_HANDLE_CLASS_COMPUTATION = 'computation-drag-handle'
export const DRAG_HANDLE_CLASS_PRESENTATION = 'presentation-drag-handle'
export const DRAG_HANDLE_CLASS_FILE = 'file-drag-handle'

/** React Flow utility class; elements with this class do not start a node drag (so inner UI is clickable). */
export const NODRAG_CLASS = 'nodrag'

/** Prevents wheel from panning/zooming the canvas when over node content. */
export const NOWHEEL_CLASS = 'nowheel'

/** Allowed types for computation block input ports (use $name in script to reference). */
export const INPUT_PORT_TYPES = ['Vector', 'Numeric', 'Symbolic', 'FuzzyBool', 'Undefined'] as const

/** Computation block output handle ids (right, top, bottom). Same result; used for edge connection point. */
export const COMPUTATION_OUTPUT_HANDLE_RIGHT = 'output'
export const COMPUTATION_OUTPUT_HANDLE_TOP = 'output-top'
export const COMPUTATION_OUTPUT_HANDLE_BOTTOM = 'output-bottom'
export const COMPUTATION_OUTPUT_HANDLES = [
  COMPUTATION_OUTPUT_HANDLE_RIGHT,
  COMPUTATION_OUTPUT_HANDLE_TOP,
  COMPUTATION_OUTPUT_HANDLE_BOTTOM,
] as const
export type ComputationOutputHandleId = (typeof COMPUTATION_OUTPUT_HANDLES)[number]

/** Debounce delay (ms) before auto-saving after graph or editor content change. */
export const AUTO_SAVE_DEBOUNCE_MS = 600

/** Maximum number of states kept in the undo stack (canvas boxes + connections). */
export const UNDO_STACK_MAX = 10
