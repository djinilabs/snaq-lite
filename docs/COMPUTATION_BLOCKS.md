# Computation blocks (visual graph)

In the visual canvas, each **computation block** is a node with an editor. You write expressions in the block; the block’s **result** is the value of the last expression. To accept data from other blocks, you add **input ports** as block properties and refer to them in the code with `$name`.

## Defining input ports

Inputs are **properties of the block**, not part of the block text. You edit them in the **Inputs** section of the block UI:

1. Click **+ Add input** on the computation block.
2. Enter a **name** (e.g. `x`, `revenue`) and choose a **type** (e.g. **Vector**, **Numeric**).
3. Use that name in the block with the `$name` syntax to refer to the value or stream from the connected upstream block (see [EXTERNAL_STREAMS.md](EXTERNAL_STREAMS.md)).

You can add several inputs; each gets a port on the left side of the block. You can remove an input with the × button. The type is used for wiring: the app checks that the source block’s output type matches the input type (e.g. Vector → Vector).

## Moving blocks

To move a computation block, drag by its **title bar** (the “Computation” label at the top). The editor and input controls (name, type, + Add input) are clickable without moving the block.

## Removing connections

To remove a connection between blocks, click the **edge** (the line between the output and input ports) to select it, then press **Delete** or **Backspace**. The connection is removed and the target block's input is unplugged.

## Example

1. Add a computation block.
2. In the block’s **Inputs** section, click **+ Add input**, set name to `x` and type to **Vector**.
3. In the editor, type `$x` (the stream from the connected input).
4. Add a second block that produces a vector (e.g. `[1, 2, 3]`).
5. Connect the second block’s output to the first block’s `x` input.
6. The first block’s result is then the stream/value from the second block.

## Summary

- **Inputs are block properties** — add and edit them in the Inputs UI on the block, not in the code.
- **Use `$name` in the script** — the block text refers to inputs by name (e.g. `$x`, `$scale`).
- **Handles appear for each input** — input ports show on the left; you connect other blocks to them.
- **Types must match** — when connecting, the source output type (e.g. Vector) must match the target input type.
- **To remove a connection** — click the edge to select it, then press Delete or Backspace.

## See also

- [EXTERNAL_STREAMS.md](EXTERNAL_STREAMS.md) — `$name` and stream semantics
- [BLOCKS_AND_EXPRESSIONS.md](BLOCKS_AND_EXPRESSIONS.md) — blocks and last expression result
- [LSP.md](LSP.md) — technical details on node signature and graph wiring
