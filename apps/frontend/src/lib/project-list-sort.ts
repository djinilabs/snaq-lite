/**
 * Sort project list by updatedAt descending (most recent first).
 * Extracted for unit testing.
 */
export function sortProjectsByUpdatedAt<T extends { updatedAt?: number }>(projects: T[]): T[] {
  return [...projects].sort((a, b) => (b.updatedAt ?? 0) - (a.updatedAt ?? 0))
}
