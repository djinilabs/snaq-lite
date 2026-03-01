/**
 * Projects list (id, name?, updatedAt?). Hydrated from localStorage on init;
 * written back when list changes.
 */

import { create } from 'zustand'
import {
  deleteProjectSnapshot,
  getProjectsIndex,
  setProjectsIndex as persistIndex,
  type ProjectMeta,
} from '~/lib/project-storage'

interface ProjectsIndexState {
  projects: ProjectMeta[]
  hydrated: boolean
  hydrate: () => void
  addProject: (meta: ProjectMeta) => void
  removeProject: (id: string) => void
  updateProjectName: (id: string, name: string) => void
  setProjects: (meta: ProjectMeta[]) => void
}

function persist(projects: ProjectMeta[]): void {
  persistIndex(projects)
}

export const useProjectsIndexStore = create<ProjectsIndexState>((set, _get) => ({
  projects: [],
  hydrated: false,

  hydrate: () => {
    const projects = getProjectsIndex()
    set({ projects, hydrated: true })
  },

  addProject: (meta) =>
    set((state) => {
      const next = [...state.projects, meta]
      persist(next)
      return { projects: next }
    }),

  removeProject: (id) => {
    deleteProjectSnapshot(id)
    set((state) => {
      const next = state.projects.filter((p) => p.id !== id)
      persist(next)
      return { projects: next }
    })
  },

  updateProjectName: (id, name) =>
    set((state) => {
      const next = state.projects.map((p) =>
        p.id === id ? { ...p, name } : p,
      )
      persist(next)
      return { projects: next }
    }),

  setProjects: (meta) => {
    persist(meta)
    set({ projects: meta })
  },
}))
