/**
 * Builds the full LSP document content for a computation node: input declarations (from UI) + body (from editor).
 * The LSP needs both so that run_node_with_graph_inputs can bind wired stream inputs to the declared names.
 */

export interface ComputationInput {
  name: string
  type: string
}

/**
 * Returns content = input decls + body when inputs exist and body does not already start with "input ";
 * otherwise returns body only. Used for didOpen/didChange so the LSP always has the full program.
 */
export function buildComputationDocumentContent(
  body: string,
  inputs?: ComputationInput[],
): string {
  const inputDecls =
    inputs
      ?.filter((i) => i.name.trim().length > 0)
      .map((i) => `input ${i.name}: ${i.type}`)
      .join('\n') ?? ''
  if (inputDecls.length === 0) return body
  return body.trimStart().startsWith('input ') ? body : `${inputDecls}\n${body}`.trim()
}
