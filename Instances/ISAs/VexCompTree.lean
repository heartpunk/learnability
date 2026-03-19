import Instances.ISAs.VexISA
import Instances.ISAs.VexLowering
import Instances.ISAs.VexLoweringCorrectness
import Instances.ISAs.VexSummaryISA
import SymExec.ProgramStructure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-!
# VexCompTree — Block/Program → CompTree bridge

Maps VEX IR blocks to `CompTree (SymSub Reg) (SymPC Reg)`, instantiated at
`vexSummaryISA Reg`. Linear statements are folded into the running partial
summary; branch statements produce `guardedChoice` nodes.

Core theorem: `treeBehavior (vexSummaryISA Reg) (blockToCompTree block) s s'`
              `↔ s' ∈ execBlockSuccs block s`
-/

/-! ## Definitions -/

/-- Build a CompTree from a statement list, carrying a partial summary forward.
    Linear stmts fold into `ps`; branch stmts produce `guardedChoice` nodes. -/
def blockToCompTree_from {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (ps : PartialSummary Reg) :
    List (Stmt Reg) → UInt64 → CompTree (SymSub Reg) (SymPC Reg)
  | [], next =>
      -- next=0 is the sentinel for Ijk_Ret and indirect branches: rip is already
      -- encoded in ps.sub via the `put rip (tmp n)` stmt added by the parser, so
      -- we apply ps.sub as-is without an additional ip_reg write.
      if next = 0 then .assign ps.sub
      else .assign (SymSub.write ps.sub ip_reg (.const next))
  | .linear stmt :: stmts, next =>
      let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
      blockToCompTree_from ip_reg { ps with sub := lowered.1, temps := lowered.2 } stmts next
  | .branch stmt :: stmts, next =>
      let bridge := branchStmtBridge ip_reg stmt
      .guardedChoice (bridge.lowerGuard ps)
        (.assign (bridge.lowerTaken ps).sub)
        (blockToCompTree_from ip_reg (bridge.lowerContinue ps) stmts next)

/-- Build a CompTree for a single VEX block. -/
def blockToCompTree {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) : CompTree (SymSub Reg) (SymPC Reg) :=
  blockToCompTree_from block.ip_reg PartialSummary.init block.stmts block.next

/-- Build a CompTree for a path (list of blocks) by sequential composition. -/
def pathToCompTree {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (path : List (Block Reg)) : CompTree (SymSub Reg) (SymPC Reg) :=
  path.foldl (fun acc block => .seq acc (blockToCompTree block)) .skip

/-! ## Bridge Proof: blockToCompTree ↔ execBlockSuccs -/

private theorem partialInit_matches' {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) :
    PartialSummaryMatches input (input, TempEnv.empty) PartialSummary.init :=
  ⟨by simp [PartialSummary.init], fun tmp => by simp [PartialSummary.init, TempEnv.empty, SymTempEnv.get_empty]⟩

private theorem treeBehavior_blockToCompTree_from {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (ps : PartialSummary Reg) (stmts : List (Stmt Reg)) (next : UInt64)
    (input : ConcreteState Reg) (concrete : ConcreteState Reg × TempEnv) (s' : ConcreteState Reg)
    (hMatch : PartialSummaryMatches input concrete ps) :
    CompTree.treeBehavior (vexSummaryISA Reg)
        (blockToCompTree_from ip_reg ps stmts next) input s' ↔
      s' ∈ execStmtsSuccs ip_reg next stmts concrete := by
  induction stmts generalizing ps concrete with
  | nil =>
    rcases concrete with ⟨state, _⟩
    have hState : state = applySymSub ps.sub input := hMatch.1
    -- Two sub-cases based on next=0 (Ijk_Ret/indirect) vs next≠0 (Ijk_Boring/Call).
    by_cases hNext : next = (0 : UInt64)
    · -- next=0: blockToCompTree_from = .assign ps.sub; execStmtsSuccs = { state }
      subst hNext
      simp only [blockToCompTree_from, if_pos rfl, CompTree.treeBehavior, assignBehavior,
        execStmtsSuccs, vexSummaryISA, show ((0 : UInt64) == 0) = true from rfl, if_true,
        Finset.mem_singleton]
      -- LHS: s' = applySymSub ps.sub input = state (by hState)
      -- RHS: s' ∈ { state }, i.e. s' = state
      exact ⟨fun h => h.trans hState.symm, fun h => h.trans hState⟩
    · -- next≠0: blockToCompTree_from = .assign (write ...); execStmtsSuccs = { state.write ... }
      simp only [blockToCompTree_from, if_neg hNext, CompTree.treeBehavior, assignBehavior,
        execStmtsSuccs, vexSummaryISA]
      simp [hNext, ← hState, applySymSub_write]
  | cons stmt stmts ih =>
    cases stmt with
    | linear stmt =>
      simp only [blockToCompTree_from, execStmtsSuccs]
      let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
      let ps' : PartialSummary Reg := { ps with sub := lowered.1, temps := lowered.2 }
      have hMatch' : PartialSummaryMatches input (execLinearStmt concrete stmt) ps' :=
        partialSummaryMatches_linearStmt_step input stmt concrete ps hMatch
      exact ih ps' (execLinearStmt concrete stmt) hMatch'
    | branch stmt =>
      simp only [blockToCompTree_from, CompTree.treeBehavior, choiceBehavior, seqBehavior,
        assertBehavior, vexSummaryISA]
      let bridge := branchStmtBridge ip_reg stmt
      have hFires : bridge.fires concrete = evalSymPC input (bridge.lowerGuard ps) :=
        bridge.fires_iff_guard input concrete ps hMatch
      have hCont : PartialSummaryMatches input (bridge.cont concrete) (bridge.lowerContinue ps) :=
        bridge.continue_matches input concrete ps hMatch
      constructor
      · -- treeBehavior → execStmtsSuccs
        -- assertBehavior gives `input = m`, so rfl would substitute input → anon. Use explicit hm.
        intro h
        rcases h with ⟨m, ⟨hSat, hm⟩, hAssign⟩ | ⟨m, ⟨hNotSat, hm⟩, hRest⟩
        · -- guard holds: taken branch (hm : m = input; rewrite m → input in hAssign)
          rw [hm] at hAssign
          simp only [assignBehavior] at hAssign
          have hGuard : bridge.fires concrete = true := hFires.trans hSat
          -- assignBehavior gives s' = applySymSub sub input, so use .trans (not .symm.trans)
          have hEq : s' = bridge.taken concrete :=
            hAssign.trans (by simpa [Summary.apply] using bridge.taken_sound input concrete ps hMatch hGuard)
          simpa [execStmtsSuccs, bridge, hGuard] using hEq
        · -- guard false: continue branch (hm : m = input; rewrite m → input in hRest)
          rw [hm] at hRest
          have hGuardFalse : bridge.fires concrete = false := by
            cases h : bridge.fires concrete with
            | false => rfl
            | true =>
              -- simp reduces satisfiesSymPC input (.not guard) → evalSymPC input guard = false
              simp [satisfiesSymPC] at hNotSat
              -- hNotSat now : evalSymPC input (expanded guard) = false
              -- hFires.symm.trans h : evalSymPC input (let-bound guard) = true
              -- both are definitionally the same expression; Eq.trans uses def-eq for middle
              exact (hFires.symm.trans h).symm.trans hNotSat
          have hMem : s' ∈ execStmtsSuccs ip_reg next stmts (bridge.cont concrete) :=
            (ih (bridge.lowerContinue ps) (bridge.cont concrete) hCont).mp hRest
          simpa [execStmtsSuccs, bridge, hGuardFalse] using hMem
      · -- execStmtsSuccs → treeBehavior
        intro hOut
        by_cases hGuard : bridge.fires concrete = true
        · -- guard holds
          have hOut' : s' = bridge.taken concrete := by
            simpa [execStmtsSuccs, bridge, hGuard] using hOut
          left
          refine ⟨input, ⟨hFires.symm.trans hGuard, rfl⟩, ?_⟩
          simp only [assignBehavior]
          rw [hOut']
          -- goal: bridge.taken concrete = applySymSub ...; taken_sound has reversed direction
          simpa [Summary.apply] using (bridge.taken_sound input concrete ps hMatch hGuard).symm
        · -- guard false
          have hGuardFalse : bridge.fires concrete = false := by
            cases h : bridge.fires concrete with
            | false => rfl
            | true => exact absurd h hGuard
          have hOut' : s' ∈ execStmtsSuccs ip_reg next stmts (bridge.cont concrete) := by
            simpa [execStmtsSuccs, bridge, hGuardFalse] using hOut
          right
          refine ⟨input, ⟨?_, rfl⟩, (ih (bridge.lowerContinue ps) (bridge.cont concrete) hCont).mpr hOut'⟩
          -- goal: satisfiesSymPC input (.not (bridge.lowerGuard ps))
          -- use show to keep the let-bound `bridge` form so simp can use hPC
          have hPC : evalSymPC input (bridge.lowerGuard ps) = false := hFires.symm.trans hGuardFalse
          show satisfiesSymPC input (.not (bridge.lowerGuard ps))
          simp [satisfiesSymPC, hPC]

/-- `treeBehavior (vexSummaryISA Reg) (blockToCompTree block) s s'`
    is equivalent to `s' ∈ execBlockSuccs block s`. -/
theorem treeBehavior_blockToCompTree {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (s s' : ConcreteState Reg) :
    CompTree.treeBehavior (vexSummaryISA Reg) (blockToCompTree block) s s' ↔
      s' ∈ execBlockSuccs block s :=
  treeBehavior_blockToCompTree_from block.ip_reg PartialSummary.init
    block.stmts block.next s (s, TempEnv.empty) s' (partialInit_matches' s)

end VexISA
