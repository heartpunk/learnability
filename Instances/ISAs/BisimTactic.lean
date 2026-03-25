import Instances.ISAs.VexSyntax
import Instances.ISAs.VexSummary
import Instances.ISAs.VexPipelineBridge
import Instances.ISAs.MemFrame
import Mathlib.Tactic.IntervalCases
import Lean

/-!
# bisim_simp tactic

Automates bisimulation proofs for generated bridge theorems.

Phase 1 (Tier 0): simp with all discovered defs — closes goals where the branch
substitution doesn't affect the closure PC.

Phase 2 (Tier 1): mem_frame peels non-overlapping writes, then tries rfl.

Phase 3 (cross-region): for remaining goals after mem_frame, tries to derive
contradiction from StackSeparation via eq_sub_of_add_eq + native_decide.
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
        if (first == 'e' || first == 'm' || first == 'p') && rest.toString.all Char.isDigit && rest.toString.length > 0 then
          result := result.push name
        else if last.startsWith "branch" && last != "branchCount" then
          result := result.push name
        else if last.startsWith "closurePC" then
          result := result.push name
        else if last.startsWith "getBranch" || last.startsWith "getClosure" then
          result := result.push name
  return result

/-- Extract function namespace from `Fin F.branchCount` in the goal. -/
private def extractFuncNS? (goalType : Expr) : MetaM (Option Name) := do
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
  -- Phase 0: intro + case split
  evalTactic (← `(tactic| intro ⟨b, hb⟩ ⟨c, hc⟩))
  evalTactic (← `(tactic| simp only [$(mkIdent (ns ++ `branchCount)):ident] at hb))
  evalTactic (← `(tactic| simp only [$(mkIdent (ns ++ `closureCount)):ident] at hc))
  evalTactic (← `(tactic| interval_cases b <;> interval_cases c))
  -- Build simp lemma syntax
  let framework := #[``substSymPC, ``evalSymPC_subst, ``applySymSub,
    ``evalSymPC, ``evalSymExpr, ``evalSymMem,
    ``ConcreteState.read, ``mask32]
  let allDefs := defs ++ framework.map id
  let mut stxLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for d in allDefs do
    stxLemmas := stxLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d):ident))
  -- Phase 1: simp with all defs (closes Tier 0)
  evalTactic (← `(tactic| all_goals simp only [$stxLemmas,*]))
  -- Check if done
  let remainingGoals ← getGoals
  if remainingGoals.isEmpty then return
  -- Phase 2: mem_frame on remaining goals (closes Tier 1)
  evalTactic (← `(tactic| all_goals first | rfl | (mem_frame; all_goals first | rfl | skip)))
  let remainingGoals ← getGoals
  if remainingGoals.isEmpty then return
  -- Phase 3: cross-region discharge on remaining goals
  -- These are hp subgoals: ∀ i j, ... → a + ofNat i ≠ b + ofNat j
  -- Try: delta StackSeparation, intro, interval_cases, eq_sub_of_add_eq, native_decide
  evalTactic (← `(tactic|
    all_goals (
      intro i j hi hj heq
      simp only [Width.byteCount] at hi hj
      try (delta StackSeparation at hsep)
      try (delta ElfPointerIntegrity at helf)
      interval_cases i <;> interval_cases j <;> (
        have h1 := UInt64.eq_sub_of_add_eq heq
        have h2 := UInt64.eq_sub_of_add_eq h1
        first
          | (rw [h2] at hsep; exact absurd hsep (by native_decide))
          | (have h := congrArg UInt64.toNat heq
             simp only [UInt64.toNat_add, UInt64.toNat, BitVec.toNat_ofNat, UInt64.size] at h hsep helf
             have := helf _ (by omega)
             omega)
          | skip))))
