import Instances.ISAs.VexCompTree
import Instances.ISAs.NextSymParserTest
import Instances.ISAs.VexProofCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-!
# NextSymDenotEval — Run `denot` on next_sym blocks

Evaluates `CompTree.denot (vexSummaryISA Amd64Reg) (blockToCompTree b)` for
parsed next_sym blocks. The symbolic denotation gives us `Finset Branch` —
each branch's `pc` is a `SymPC Amd64Reg` path condition describing which
concrete inputs take that execution path.

This is Phase E step 4-5: inspect the branch structure of each block,
then the PCs partition the input space into token classes (grammar extraction).

Note: `#eval` here runs at build time and output appears in the build log.
We use `#eval` (not `#guard`) because `denot` involves large symbolic terms
that are slow to reduce via kernel definitional equality.
-/

/-! ## Branch count summary: all 60 blocks -/

-- For each block: print (block_index, bound, denot.card)
-- bound is structural (no ISA), card requires running symbolic execution.
#eval do
  IO.println "Block | bound | denot.card"
  IO.println "------|-------|----------"
  let mut i := 0
  for s in nextSymBlocks do
    match parseIRSB s with
    | .error e => IO.println s!"Block {i}: PARSE ERROR: {e}"
    | .ok b =>
      let tree := blockToCompTree b
      let bnd := CompTree.bound tree
      let card := (CompTree.denot (vexSummaryISA Amd64Reg) tree).card
      IO.println s!"{i} | {bnd} | {card}"
    i := i + 1

/-! ## Guard conditions for branching blocks -/

-- Finset.toList is noncomputable, so we inspect the CompTree AST directly.
-- For a single-branch-point block, the top-level node is a guardedChoice
-- and the guard IS the path condition for the taken branch.
-- This is equivalent to reading the denot output PCs for simple blocks.
#eval do
  IO.println "Branching block guard PCs:"
  let mut i := 0
  for s in nextSymBlocks do
    match parseIRSB s with
    | .error _ => pure ()
    | .ok b =>
      let tree := blockToCompTree b
      match tree with
      | .guardedChoice guard _ _ =>
        IO.println s!"  Block {i}: {repr guard}"
      | _ => pure ()
    i := i + 1

/-! ## P₀ analysis: count distinct data guard PCs -/

#eval do
  IO.println "\nP₀ analysis — data guard PCs across all next_sym blocks:"
  let mut allGuards : List (SymPC Amd64Reg) := []
  for s in nextSymBlocks do
    match parseIRSB s with
    | .error _ => pure ()
    | .ok b =>
      let tree := blockToCompTree b
      allGuards := allGuards ++ collectGuardPCsList tree
  let deduped := allGuards.eraseDups
  let routing := deduped.filter (SymPC.isRoutingPC Amd64Reg.rip)
  let dataPCs := dataGuardPCsList Amd64Reg.rip deduped
  IO.println s!"Total distinct guard PCs: {deduped.length}"
  IO.println s!"Routing PCs (rip == const): {routing.length}"
  IO.println s!"Data PCs (P₀): {dataPCs.length}"
  IO.println s!"2^P₀ = {2 ^ dataPCs.length}"
  IO.println "Data PCs:"
  for pc in dataPCs do
    IO.println s!"  {repr pc}"
