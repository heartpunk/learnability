import Instances.ISAs.VexCompTree
import Instances.ISAs.ParserNTParserTest
import Instances.ISAs.NextSymParserTest
import Instances.ISAs.VexProofCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-!
# ParserNTDenotEval — Run `denot` on Tiny C parser NT blocks

Evaluates `CompTree.denot (vexSummaryISA Amd64Reg) (blockToCompTree b)` for
each block of the 6 parser non-terminals: term, sum, test, expr, paren_expr,
statement.

The symbolic denotation gives `Finset Branch` — each branch's `pc` is a
`SymPC Amd64Reg` path condition describing which concrete inputs take that
execution path. These path conditions ARE the grammar of the NT functions.

This is Phase F step 5: inspect the branch structure, verify token-class
conditions appear in NT path conditions, compare against STALAGMITE grammar.

Note: `#eval` runs at build time; output appears in the build log.
-/

def ntFunctions : List (String × List String) :=
  [ ("term", termBlocks)
  , ("sum", sumBlocks)
  , ("test", testBlocks)
  , ("expr", exprBlocks)
  , ("paren_expr", paren_exprBlocks)
  , ("statement", statementBlocks) ]

/-! ## Branch count summary per NT function -/

#eval do
  IO.println "NT Function | Block | bound | denot.card"
  IO.println "------------|-------|-------|----------"
  for (name, blocks) in ntFunctions do
    let mut i := 0
    for s in blocks do
      match parseIRSB s with
      | .error e => IO.println s!"{name} block {i}: PARSE ERROR: {e}"
      | .ok b =>
        let tree := blockToCompTree b
        let bnd := CompTree.bound tree
        let card := (CompTree.denot (vexSummaryISA Amd64Reg) tree).card
        IO.println s!"{name} | {i} | {bnd} | {card}"
      i := i + 1

/-! ## Guard conditions for branching blocks per NT -/

#eval do
  IO.println "Branching block guard PCs per NT:"
  for (name, blocks) in ntFunctions do
    IO.println s!"--- {name} ---"
    let mut i := 0
    for s in blocks do
      match parseIRSB s with
      | .error _ => pure ()
      | .ok b =>
        let tree := blockToCompTree b
        match tree with
        | .guardedChoice guard _ _ =>
          IO.println s!"  block {i}: {repr guard}"
        | _ => pure ()
      i := i + 1

/-! ## P₀ analysis: count distinct data guard PCs across all NT functions -/

#eval do
  IO.println "\nP₀ analysis — data guard PCs across all parser NT blocks:"
  let mut allGuards : List (SymPC Amd64Reg) := []
  for (_, blocks) in ntFunctions do
    for s in blocks do
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

/-! ## Per-function P₀ breakdown -/

#eval do
  IO.println "\nPer-function P₀ breakdown:"
  -- next_sym
  let mut nsGuards : List (SymPC Amd64Reg) := []
  for s in nextSymBlocks do
    match parseIRSB s with
    | .error _ => pure ()
    | .ok b => nsGuards := nsGuards ++ collectGuardPCsList (blockToCompTree b)
  let nsData := dataGuardPCsList Amd64Reg.rip nsGuards.eraseDups
  IO.println s!"  next_sym: P₀ = {nsData.length}, 2^P₀ = {2 ^ nsData.length}"
  -- Each NT function
  for (name, blocks) in ntFunctions do
    let mut guards : List (SymPC Amd64Reg) := []
    for s in blocks do
      match parseIRSB s with
      | .error _ => pure ()
      | .ok b => guards := guards ++ collectGuardPCsList (blockToCompTree b)
    let dataPCs := dataGuardPCsList Amd64Reg.rip guards.eraseDups
    IO.println s!"  {name}: P₀ = {dataPCs.length}, 2^P₀ = {2 ^ dataPCs.length}"
