/**
 * Optional API client for a future backend. Base URL from VITE_API_BASE_URL.
 * Backend is independent of TanStack Start (no server routes in this app).
 */

export function getBaseUrl(): string {
  return (import.meta.env?.VITE_API_BASE_URL as string) ?? ''
}

export function apiFetch(path: string, init?: RequestInit): Promise<Response> {
  const base = getBaseUrl()
  const url = base ? `${base.replace(/\/$/, '')}/${path.replace(/^\//, '')}` : path
  return fetch(url, init)
}
