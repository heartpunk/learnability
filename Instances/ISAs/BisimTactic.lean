import Instances.ISAs.VexSyntax
import Instances.ISAs.VexSummary
import Instances.ISAs.VexPipelineBridge
import Instances.ISAs.MemFrame
import Mathlib.Tactic.IntervalCases
import Lean

/-!
# bisim_simp tactic

Automates Tier 0 bisimulation proofs for generated bridge theorems.
-/

open Lean Meta Elab Tactic
open VexISA

/-- Collect all definition names in a namespace that look like generated defs. -/
private def collectSimpDefs (env : Environment) (ns : Name) : Array Name := Id.run do
  let mut result : Array Name := #[]
  for (name, _) in env.constants.map₁.toList do
    if name.getPrefix == ns then
      let last := name.componentsRev.head!.toString
      if last.length > 0 then
        let first := last.get ⟨0⟩
        let rest := last.toSubstring.drop 1
        -- eN, mN, pN (shared defs)
        if (first == 'e' || first == 'm' || first == 'p') && rest.toString.all Char.isDigit && rest.toString.length > 0 then
          result := result.push name
        -- branchN, closurePCN
        else if last.startsWith "branch" && last != "branchCount" then
          result := result.push name
        else if last.startsWith "closurePC" then
          result := result.push name
        -- getBranchAux, getBranchChunkN, getClosureAux
        else if last.startsWith "getBranch" || last.startsWith "getClosure" then
          result := result.push name
  return result

/-- Extract function namespace from `Fin F.branchCount` in the goal. -/
private def extractFuncNS? (goalType : Expr) : MetaM (Option Name) := do
  -- Goal: ∀ b : Fin F.branchCount, ...
  match goalType with
  | .forallE _ binderTy _ _ =>
    let (fn, args) := binderTy.getAppFnArgs
    if fn == ``Fin && args.size == 1 then
      let bcExpr := args[0]!
      let (bcFn, _) := bcExpr.getAppFnArgs
      if bcFn.componentsRev.head!.toString == "branchCount" then
        return some bcFn.getPrefix
    return none
  | _ => return none

elab "bisim_simp" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some ns ← goal.withContext (extractFuncNS? goalType)
    | throwError "bisim_simp: could not extract function namespace from goal"
  let env ← getEnv
  let defs := collectSimpDefs env ns
  logInfo m!"bisim_simp: {ns}, {defs.size} defs"
  -- intro ⟨b, hb⟩ ⟨c, hc⟩
  evalTactic (← `(tactic| intro ⟨b, hb⟩ ⟨c, hc⟩))
  -- Reduce bounds
  evalTactic (← `(tactic| simp only [$(mkIdent (ns ++ `branchCount)):ident] at hb))
  evalTactic (← `(tactic| simp only [$(mkIdent (ns ++ `closureCount)):ident] at hc))
  -- Case split
  evalTactic (← `(tactic| interval_cases b <;> interval_cases c))
  -- Build simp lemma list
  -- Framework lemmas — use `open VexISA in` resolved names
  let framework := #[``substSymPC, ``evalSymPC_subst, ``applySymSub,
    ``evalSymPC, ``evalSymExpr, ``evalSymMem,
    ``ConcreteState.read, ``mask32]
  let allDefs := defs ++ framework.map id
  let mut stxLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for d in allDefs do
    stxLemmas := stxLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d):ident))
  -- Apply simp to all goals
  evalTactic (← `(tactic| all_goals simp only [$stxLemmas,*]))
