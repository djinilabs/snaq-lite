/**
 * Layout helpers for ComputationBoxNode: min height and input handle vertical positions.
 * Kept in a separate module for unit testing.
 */

const HEADER_OFFSET = 32
const HANDLE_STEP = 24
const BOTTOM_PADDING = 16
const MIN_HEIGHT_BASE = 120

/**
 * Minimum height for the node so all input handles fit below the header with padding.
 * Clamps inputCount to >= 0 to avoid negative values from bad data.
 */
export function computationNodeMinHeight(inputCount: number): number {
  const n = Math.max(0, inputCount)
  return Math.max(MIN_HEIGHT_BASE, HEADER_OFFSET + n * HANDLE_STEP + BOTTOM_PADDING)
}

/**
 * Vertical offset (top in px) for the i-th input handle (0-based).
 * Clamps index to >= 0.
 */
export function computationNodeHandleTop(index: number): number {
  return HEADER_OFFSET + Math.max(0, index) * HANDLE_STEP
}
