import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Phase4LoopStabilization

inductive LoopReg where
  | r0
  | r1
  | r2
  deriving DecidableEq, Repr

instance : Fintype LoopReg where
  elems := {LoopReg.r0, LoopReg.r1, LoopReg.r2}
  complete := by
    intro r
    cases r <;> simp

abbrev Reg := LoopReg

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def blockA : Block Reg :=
  { stmts := [Stmt.branch (BranchStmt.exit (Cond.eq64 (.get .r0) (.const 0)) 0x10)]
    ip_reg := .r1
    next := 0x20 }

/-- Left branch reset: write r0 then r2. -/
def blockB : Block Reg :=
  { stmts := [Stmt.put .r0 (.const 0), Stmt.put .r2 (.const 0)]
    ip_reg := .r1
    next := 0 }

/-- Right branch reset: write r2 then r0. Same semantics, different syntax. -/
def blockC : Block Reg :=
  { stmts := [Stmt.put .r2 (.const 0), Stmt.put .r0 (.const 0)]
    ip_reg := .r1
    next := 0 }

def pathLeft : List (Block Reg) := [blockA, blockB]
def pathRight : List (Block Reg) := [blockA, blockC]
def bodyPaths : Finset (List (Block Reg)) := {pathLeft, pathRight}

def guard : SymPC Reg := .eq (.reg .r0) (.const 0)

def resetState (s : ConcreteState Reg) : ConcreteState Reg :=
  { regs := fun
      | .r0 => 0
      | .r1 => 0
      | .r2 => 0
    mem := s.mem }

private theorem lowerBlockSub_blockB_apply (s : ConcreteState Reg) :
    applySymSub (lowerBlockSub blockB) s = resetState s := by
  apply ConcreteState.ext
  · funext r
    cases r <;> simp [lowerBlockSub, lowerStmts, lowerStmt, lowerLinearStmt,
      linearStmtBridge, lowerExpr, blockB, SymSub.write, applySymSub, resetState]
  · simp [lowerBlockSub, lowerStmts, lowerStmt, lowerLinearStmt,
      linearStmtBridge, lowerExpr, blockB, SymSub.write, applySymSub, resetState, SymSub.id]

private theorem lowerBlockSub_blockC_apply (s : ConcreteState Reg) :
    applySymSub (lowerBlockSub blockC) s = resetState s := by
  apply ConcreteState.ext
  · funext r
    cases r <;> simp [lowerBlockSub, lowerStmts, lowerStmt, lowerLinearStmt,
      linearStmtBridge, lowerExpr, blockC, SymSub.write, applySymSub, resetState]
  · simp [lowerBlockSub, lowerStmts, lowerStmt, lowerLinearStmt,
      linearStmtBridge, lowerExpr, blockC, SymSub.write, applySymSub, resetState, SymSub.id]

private theorem execBlock_blockB_eq_resetState (s : ConcreteState Reg) :
    execBlock blockB s = resetState s := by
  calc
    execBlock blockB s = applySymSub (lowerBlockSub blockB) s := by
      symm
      exact lowerBlockSub_sound blockB s
    _ = resetState s := lowerBlockSub_blockB_apply s

private theorem execBlock_blockC_eq_resetState (s : ConcreteState Reg) :
    execBlock blockC s = resetState s := by
  calc
    execBlock blockC s = applySymSub (lowerBlockSub blockC) s := by
      symm
      exact lowerBlockSub_sound blockC s
    _ = resetState s := lowerBlockSub_blockC_apply s

def loop : VexLoopSummary Reg where
  body := CompTree.guardedChoice guard (CompTree.assign (lowerBlockSub blockB)) (CompTree.assign (lowerBlockSub blockC))
  continues := .true
  exits := .not .true
  bodyEffect := resetState
  bodyEffect_spec := by
    intro s s'
    by_cases h : (vexSummaryISA Reg).satisfies s guard
    · constructor
      · intro hTree
        have hTree' := hTree
        simp [CompTree.treeBehavior, choiceBehavior, seqBehavior, assertBehavior, assignBehavior, h] at hTree'
        rcases hTree' with hB | hImpossible
        · exact hB.trans (lowerBlockSub_blockB_apply s)
        · have : False := by
            have hNot : ¬ (vexSummaryISA Reg).satisfies s guard := by
              simpa [vexSummaryISA, satisfiesSymPC, evalSymPC] using hImpossible.1
            exact hNot h
          exact this.elim
      · intro hs'
        simp [CompTree.treeBehavior, choiceBehavior, seqBehavior, assertBehavior, assignBehavior, h]
        cases hs'
        exact Or.inl (lowerBlockSub_blockB_apply s).symm
    · constructor
      · intro hTree
        have hTree' := hTree
        simp [CompTree.treeBehavior, choiceBehavior, seqBehavior, assertBehavior, assignBehavior, h] at hTree'
        exact hTree'.2.trans (lowerBlockSub_blockC_apply s)
      · intro hs'
        simp [CompTree.treeBehavior, choiceBehavior, seqBehavior, assertBehavior, assignBehavior, h]
        refine ⟨?_, ?_⟩
        · simpa [vexSummaryISA, satisfiesSymPC, evalSymPC] using h
        · cases hs'
          exact (lowerBlockSub_blockC_apply s).symm
  guard_partition := by
    intro s
    simp [vexSummaryISA, satisfiesSymPC, evalSymPC]

private theorem bodyEffect_executes_and_changes :
    let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 5
          | .r1 => 0
          | .r2 => 99
        mem := [] }
    loop.bodyEffect s ≠ s := by
  dsimp [loop, resetState]
  intro h
  have h' : (0 : UInt64) = 99 := by
    have h'' := congrArg (fun st => st.read .r2) h
    simp [ConcreteState.read] at h''
  have hcontra : ¬ ((0 : UInt64) = 99) := by native_decide
  exact hcontra h'

def blockATakenSummary : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x10)
  , pc := .and .true (.eq (.reg .r0) (.const 0)) }

def blockAFallSummary : Summary Reg :=
  { sub := SymSub.write SymSub.id .r1 (.const 0x20)
  , pc := .and .true (.not (.eq (.reg .r0) (.const 0))) }

def resetSummaryB : Summary Reg := Summary.compose (lowerBlock blockB) Summary.id
def resetSummaryC : Summary Reg := Summary.compose (lowerBlock blockC) Summary.id

def expectedLeft : Summary Reg := Summary.compose blockATakenSummary resetSummaryB
def expectedRight : Summary Reg := Summary.compose blockAFallSummary resetSummaryC

def closure : Finset (SymPC Reg) := {expectedLeft.pc, expectedRight.pc}

def K : Nat := 1

private theorem expectedLeft_mem : expectedLeft ∈ lowerBlockPathSummaries pathLeft := by
  native_decide

private theorem expectedRight_mem : expectedRight ∈ lowerBlockPathSummaries pathRight := by
  native_decide

private theorem resetSummaryB_enabled (s : ConcreteState Reg) :
    Summary.enabled resetSummaryB s := by
  rw [resetSummaryB]
  refine (Summary.compose_enabled_iff (lowerBlock blockB) Summary.id s).2 ?_
  constructor
  · simp [lowerBlock, Summary.enabled, satisfiesSymPC]
  · simp [Summary.id, Summary.enabled, satisfiesSymPC]

private theorem resetSummaryC_enabled (s : ConcreteState Reg) :
    Summary.enabled resetSummaryC s := by
  rw [resetSummaryC]
  refine (Summary.compose_enabled_iff (lowerBlock blockC) Summary.id s).2 ?_
  constructor
  · simp [lowerBlock, Summary.enabled, satisfiesSymPC]
  · simp [Summary.id, Summary.enabled, satisfiesSymPC]

private theorem expectedLeft_apply (s : ConcreteState Reg) :
    Summary.apply expectedLeft s = resetState s := by
  calc
    Summary.apply expectedLeft s
        = Summary.apply resetSummaryB (Summary.apply blockATakenSummary s) := by
            simp [expectedLeft]
    _ = Summary.apply (lowerBlock blockB) (Summary.apply blockATakenSummary s) := by
            simp [resetSummaryB]
    _ = execBlock blockB (Summary.apply blockATakenSummary s) := by
            simpa [Summary.apply] using lowerBlock_sound blockB (Summary.apply blockATakenSummary s)
    _ = resetState (Summary.apply blockATakenSummary s) := execBlock_blockB_eq_resetState _
    _ = resetState s := by
            apply ConcreteState.ext
            · funext r
              cases r <;> rfl
            · rfl

private theorem expectedRight_apply (s : ConcreteState Reg) :
    Summary.apply expectedRight s = resetState s := by
  calc
    Summary.apply expectedRight s
        = Summary.apply resetSummaryC (Summary.apply blockAFallSummary s) := by
            simp [expectedRight]
    _ = Summary.apply (lowerBlock blockC) (Summary.apply blockAFallSummary s) := by
            simp [resetSummaryC]
    _ = execBlock blockC (Summary.apply blockAFallSummary s) := by
            simpa [Summary.apply] using lowerBlock_sound blockC (Summary.apply blockAFallSummary s)
    _ = resetState (Summary.apply blockAFallSummary s) := execBlock_blockC_eq_resetState _
    _ = resetState s := by
            apply ConcreteState.ext
            · funext r
              cases r <;> rfl
            · rfl

private theorem hstep : BodyPathStepRealizable loop bodyPaths closure := by
  intro s
  by_cases hZero : s.read .r0 = 0
  · let cls : LiveBranchClass Reg :=
      { path := pathLeft
        summary := expectedLeft
        signature := pcSignatureWith (vexSummaryISA Reg) closure s }
    refine ⟨cls, ?_⟩
    change cls.RealizesBodyStep loop bodyPaths closure s
    unfold LiveBranchClass.RealizesBodyStep LiveBranchClass.Realizes
    dsimp [cls]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨by simp [bodyPaths], expectedLeft_mem, ?_, rfl⟩
      have hA : Summary.enabled blockATakenSummary s := by
        change evalSymPC s (.and .true (.eq (.reg .r0) (.const 0))) = true
        simpa [evalSymPC, hZero]
      have hB : Summary.enabled resetSummaryB (Summary.apply blockATakenSummary s) := resetSummaryB_enabled _
      exact (Summary.compose_enabled_iff blockATakenSummary resetSummaryB s).2 ⟨hA, hB⟩
    · simpa [loop] using expectedLeft_apply s
    · have hEnabled : Summary.enabled expectedLeft s := by
        have hA : Summary.enabled blockATakenSummary s := by
          change evalSymPC s (.and .true (.eq (.reg .r0) (.const 0))) = true
          simpa [evalSymPC, hZero]
        have hB : Summary.enabled resetSummaryB (Summary.apply blockATakenSummary s) := resetSummaryB_enabled _
        exact (Summary.compose_enabled_iff blockATakenSummary resetSummaryB s).2 ⟨hA, hB⟩
      have hMemSucc : resetState s ∈ summarySuccs (lowerBlockPathSummaries pathLeft) s := by
        exact (mem_summarySuccs (lowerBlockPathSummaries pathLeft) s (resetState s)).2
          ⟨expectedLeft, expectedLeft_mem, hEnabled, expectedLeft_apply s⟩
      simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath pathLeft s] using hMemSucc
  · let cls : LiveBranchClass Reg :=
      { path := pathRight
        summary := expectedRight
        signature := pcSignatureWith (vexSummaryISA Reg) closure s }
    refine ⟨cls, ?_⟩
    change cls.RealizesBodyStep loop bodyPaths closure s
    unfold LiveBranchClass.RealizesBodyStep LiveBranchClass.Realizes
    dsimp [cls]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨by simp [bodyPaths], expectedRight_mem, ?_, rfl⟩
      have hA : Summary.enabled blockAFallSummary s := by
        change evalSymPC s (.and .true (.not (.eq (.reg .r0) (.const 0)))) = true
        have hZero' : ¬ s.regs .r0 = 0 := by simpa using hZero
        simp [evalSymPC, hZero']
      have hC : Summary.enabled resetSummaryC (Summary.apply blockAFallSummary s) := resetSummaryC_enabled _
      exact (Summary.compose_enabled_iff blockAFallSummary resetSummaryC s).2 ⟨hA, hC⟩
    · simpa [loop] using expectedRight_apply s
    · have hEnabled : Summary.enabled expectedRight s := by
        have hA : Summary.enabled blockAFallSummary s := by
          change evalSymPC s (.and .true (.not (.eq (.reg .r0) (.const 0)))) = true
          have hZero' : ¬ s.regs .r0 = 0 := by simpa using hZero
          simp [evalSymPC, hZero']
        have hC : Summary.enabled resetSummaryC (Summary.apply blockAFallSummary s) := resetSummaryC_enabled _
        exact (Summary.compose_enabled_iff blockAFallSummary resetSummaryC s).2 ⟨hA, hC⟩
      have hMemSucc : resetState s ∈ summarySuccs (lowerBlockPathSummaries pathRight) s := by
        exact (mem_summarySuccs (lowerBlockPathSummaries pathRight) s (resetState s)).2
          ⟨expectedRight, expectedRight_mem, hEnabled, expectedRight_apply s⟩
      simpa [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath pathRight s] using hMemSucc

private theorem bodyEffect_idempotent (s : ConcreteState Reg) :
    resetState (resetState s) = resetState s := by
  apply ConcreteState.ext
  · funext r
    cases r <;> rfl
  · rfl

private theorem bodyEffect_iterate_pos (s : ConcreteState Reg) :
    ∀ n, 0 < n → loop.bodyEffect^[n] s = loop.bodyEffect^[1] s := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rw [ih (Nat.succ_pos _)]
      simpa [loop, Function.iterate_one] using bodyEffect_idempotent s

private theorem hcycle : ∀ s n, K < n → loop.bodyEffect^[n] s = loop.bodyEffect^[1] s := by
  intro s n hn
  exact bodyEffect_iterate_pos s n (by omega)

private theorem hstable : BranchClassesStable loop bodyPaths closure K := by
  apply branchClassesStable_of_orbit_cycling
  · exact hstep
  · intro s n hn
    refine ⟨1, by simp [K], ?_⟩
    simpa [Function.iterate_one] using hcycle s n hn

example :
    let s : ConcreteState Reg :=
      { regs := fun
          | .r0 => 5
          | .r1 => 0
          | .r2 => 99
        mem := [] }
    loop.bodyEffect s ≠ s :=
  bodyEffect_executes_and_changes

example : BodyPathStepRealizable loop bodyPaths closure := hstep

example : BranchClassesStable loop bodyPaths closure K := hstable

end Instances.Examples.Phase4LoopStabilization
