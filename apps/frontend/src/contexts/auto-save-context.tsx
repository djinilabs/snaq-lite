import { createContext, useContext } from 'react'

export interface AutoSaveContextValue {
  requestSave: () => void
}

export const AutoSaveContext = createContext<AutoSaveContextValue | null>(null)

export function useAutoSave(): AutoSaveContextValue | null {
  return useContext(AutoSaveContext)
}
