import Instances.Examples.Phase4LoopStabilization
import Instances.ISAs.VexWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples.Phase5Capstone

abbrev Reg := Instances.Examples.Phase4LoopStabilization.Reg
abbrev blockA := Instances.Examples.Phase4LoopStabilization.blockA
abbrev blockB := Instances.Examples.Phase4LoopStabilization.blockB
abbrev blockC := Instances.Examples.Phase4LoopStabilization.blockC
abbrev pathLeft := Instances.Examples.Phase4LoopStabilization.pathLeft
abbrev pathRight := Instances.Examples.Phase4LoopStabilization.pathRight
abbrev bodyPaths := Instances.Examples.Phase4LoopStabilization.bodyPaths
abbrev guard := Instances.Examples.Phase4LoopStabilization.guard
abbrev resetState := Instances.Examples.Phase4LoopStabilization.resetState
abbrev blockATakenSummary := Instances.Examples.Phase4LoopStabilization.blockATakenSummary
abbrev blockAFallSummary := Instances.Examples.Phase4LoopStabilization.blockAFallSummary
abbrev resetSummaryB := Instances.Examples.Phase4LoopStabilization.resetSummaryB
abbrev resetSummaryC := Instances.Examples.Phase4LoopStabilization.resetSummaryC
abbrev expectedLeft := Instances.Examples.Phase4LoopStabilization.expectedLeft
abbrev expectedRight := Instances.Examples.Phase4LoopStabilization.expectedRight
abbrev closure := Instances.Examples.Phase4LoopStabilization.closure

noncomputable local instance :
    ∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ) := by
  intro s φ
  simpa [satisfiesSymPC] using
    (inferInstance : Decidable (evalSymPC s φ = true))

def loop : VexLoopSummary Reg where
  body := Instances.Examples.Phase4LoopStabilization.loop.body
  continues := .not (.eq (.reg .r2) (.const 0))
  exits := .eq (.reg .r2) (.const 0)
  bodyEffect := resetState
  bodyEffect_spec := Instances.Examples.Phase4LoopStabilization.loop.bodyEffect_spec
  guard_partition := by
    intro s
    simp [vexSummaryISA, satisfiesSymPC, evalSymPC]

def K : Nat := 1

def Relevant : ConcreteState Reg → Prop := fun _ => True

def observe (_ : ConcreteState Reg) : PUnit := PUnit.unit

def program : Program Reg where
  blocks := fun _ => none

private theorem pathLeft_mem_bodyPaths : pathLeft ∈ bodyPaths := by
  exact Finset.mem_insert.mpr <| Or.inl rfl

private theorem pathRight_mem_bodyPaths : pathRight ∈ bodyPaths := by
  exact Finset.mem_insert.mpr <| Or.inr (by simp)

private theorem expectedLeft_mem : expectedLeft ∈ lowerBlockPathSummaries pathLeft := by
  native_decide

private theorem expectedRight_mem : expectedRight ∈ lowerBlockPathSummaries pathRight := by
  native_decide

private theorem expectedLeft_sub_regs (r : Reg) :
    expectedLeft.sub.regs r = .const 0 := by
  cases r <;> native_decide

private theorem expectedRight_sub_regs (r : Reg) :
    expectedRight.sub.regs r = .const 0 := by
  cases r <;> native_decide

private theorem expectedLeft_sub_mem :
    expectedLeft.sub.mem = .base := by
  native_decide

private theorem expectedRight_sub_mem :
    expectedRight.sub.mem = .base := by
  native_decide

private theorem lowerBlockSub_blockB_apply (s : ConcreteState Reg) :
    applySymSub (lowerBlockSub blockB) s = resetState s := by
  have hSub :
      lowerBlockSub blockB =
        SymSub.write
          (SymSub.write
            (SymSub.write SymSub.id .r0 (.const 0))
            .r2 (.const 0))
          .r1 (.const 0) := by
    native_decide
  rw [hSub]
  apply ConcreteState.ext
  · funext r
    cases r <;> rfl
  · rfl

private theorem lowerBlockSub_blockC_apply (s : ConcreteState Reg) :
    applySymSub (lowerBlockSub blockC) s = resetState s := by
  have hSub :
      lowerBlockSub blockC =
        SymSub.write
          (SymSub.write
            (SymSub.write SymSub.id .r2 (.const 0))
            .r0 (.const 0))
          .r1 (.const 0) := by
    native_decide
  rw [hSub]
  apply ConcreteState.ext
  · funext r
    cases r <;> rfl
  · rfl

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
  change Summary.apply (Summary.compose blockATakenSummary resetSummaryB) s = resetState s
  calc
    Summary.apply (Summary.compose blockATakenSummary resetSummaryB) s
        = Summary.apply resetSummaryB (Summary.apply blockATakenSummary s) := by
            simp
    _ = Summary.apply (lowerBlock blockB) (Summary.apply blockATakenSummary s) := by
            change Summary.apply (Summary.compose (lowerBlock blockB) Summary.id)
                (Summary.apply blockATakenSummary s) =
              Summary.apply (lowerBlock blockB) (Summary.apply blockATakenSummary s)
            simp
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
  change Summary.apply (Summary.compose blockAFallSummary resetSummaryC) s = resetState s
  calc
    Summary.apply (Summary.compose blockAFallSummary resetSummaryC) s
        = Summary.apply resetSummaryC (Summary.apply blockAFallSummary s) := by
            simp
    _ = Summary.apply (lowerBlock blockC) (Summary.apply blockAFallSummary s) := by
            change Summary.apply (Summary.compose (lowerBlock blockC) Summary.id)
                (Summary.apply blockAFallSummary s) =
              Summary.apply (lowerBlock blockC) (Summary.apply blockAFallSummary s)
            simp
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
    · refine ⟨pathLeft_mem_bodyPaths, expectedLeft_mem, ?_, rfl⟩
      have hA : Summary.enabled blockATakenSummary s := by
        change evalSymPC s (.and .true (.eq (.reg .r0) (.const 0))) = true
        simpa [evalSymPC, hZero]
      have hB : Summary.enabled resetSummaryB
          (Summary.apply blockATakenSummary s) := resetSummaryB_enabled _
      exact (Summary.compose_enabled_iff _ _ s).2 ⟨hA, hB⟩
    · simpa [loop] using expectedLeft_apply s
    · have hEnabled : Summary.enabled expectedLeft s := by
        have hA : Summary.enabled blockATakenSummary s := by
          change evalSymPC s (.and .true (.eq (.reg .r0) (.const 0))) = true
          simpa [evalSymPC, hZero]
        have hB : Summary.enabled resetSummaryB
            (Summary.apply blockATakenSummary s) := resetSummaryB_enabled _
        exact (Summary.compose_enabled_iff _ _ s).2 ⟨hA, hB⟩
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
    · refine ⟨pathRight_mem_bodyPaths, expectedRight_mem, ?_, rfl⟩
      have hA : Summary.enabled blockAFallSummary s := by
        change evalSymPC s (.and .true (.not (.eq (.reg .r0) (.const 0)))) = true
        have hZero' : ¬ s.regs Phase4LoopStabilization.LoopReg.r0 = 0 := by
          simpa [ConcreteState.read] using hZero
        simp [evalSymPC, hZero']
      have hC : Summary.enabled resetSummaryC
          (Summary.apply blockAFallSummary s) := resetSummaryC_enabled _
      exact (Summary.compose_enabled_iff _ _ s).2 ⟨hA, hC⟩
    · simpa [loop] using expectedRight_apply s
    · have hEnabled : Summary.enabled expectedRight s := by
        have hA : Summary.enabled blockAFallSummary s := by
          change evalSymPC s (.and .true (.not (.eq (.reg .r0) (.const 0)))) = true
          have hZero' : ¬ s.regs Phase4LoopStabilization.LoopReg.r0 = 0 := by
            simpa [ConcreteState.read] using hZero
          simp [evalSymPC, hZero']
        have hC : Summary.enabled resetSummaryC
            (Summary.apply blockAFallSummary s) := resetSummaryC_enabled _
        exact (Summary.compose_enabled_iff _ _ s).2 ⟨hA, hC⟩
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

private theorem bodyEffect_iterate_succ_eq_one (s : ConcreteState Reg) :
    ∀ n, loop.bodyEffect^[n + 1] s = loop.bodyEffect^[1] s := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Nat.add_assoc, Function.iterate_succ_apply']
      rw [ih]
      simpa [Function.iterate_one] using bodyEffect_idempotent s

private theorem bodyEffect_iterate_pos (s : ConcreteState Reg) :
    ∀ n, 0 < n → loop.bodyEffect^[n] s = loop.bodyEffect^[1] s := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simpa [Nat.add_comm] using bodyEffect_iterate_succ_eq_one s m

private theorem hcycle : ∀ s n, K < n → loop.bodyEffect^[n] s = loop.bodyEffect^[1] s := by
  intro s n hn
  exact bodyEffect_iterate_pos s n (by omega)

private theorem hstable : BranchClassesStable loop bodyPaths closure K := by
  apply branchClassesStable_of_orbit_cycling
  · exact hstep
  · intro s n hn
    refine ⟨1, by simp [K], ?_⟩
    simpa [Function.iterate_one] using hcycle s n hn

private theorem hobs : PCObserveInvariant closure observe := by
  intro s₁ s₂ _
  rfl

private theorem whileBehavior_zero_of_exits {s : ConcreteState Reg}
    (hExit : (vexSummaryISA Reg).satisfies s loop.exits) :
    whileBehavior (isa := vexSummaryISA Reg) loop s s := by
  refine ⟨0, rfl, ?_, hExit⟩
  intro k hk
  exact (Nat.not_lt_zero _ hk).elim

private theorem whileBehavior_one_of_continues {s : ConcreteState Reg}
    (hCont : (vexSummaryISA Reg).satisfies s loop.continues) :
    whileBehavior (isa := vexSummaryISA Reg) loop s (resetState s) := by
  refine ⟨1, ?_, ?_, ?_⟩
  · simp [iterateBody, loop]
  · intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    simpa using hCont
  · exact rfl

private theorem hsound :
    BranchingLoopWitnessSound
      (whileLoopRegionSpec program .r1 loop Relevant observe)
      bodyPaths K := by
  intro s o hExec
  rcases hExec with ⟨blocks, hMem, hExecBlocks⟩
  rcases hExecBlocks with ⟨hRel, s', hPath, hObs⟩
  refine ⟨hRel, ?_⟩
  by_cases hExit : (vexSummaryISA Reg).satisfies s loop.exits
  · refine ⟨s, whileBehavior_zero_of_exits hExit, ?_⟩
    cases o
    rfl
  · have hCont : (vexSummaryISA Reg).satisfies s loop.continues := by
      exact (loop.guard_partition s).mpr (by
        simpa [vexSummaryISA, satisfiesSymPC, evalSymPC] using hExit)
    refine ⟨resetState s, whileBehavior_one_of_continues hCont, ?_⟩
    cases o
    rfl

example : branchingLoopWitness bodyPaths K = {[], pathLeft, pathRight} := by
  native_decide

example : BranchingLoopWitnessComplete
    (whileLoopRegionSpec program .r1 loop Relevant observe)
    bodyPaths K := by
  exact whileBranchingLoopWitnessComplete_of_branchClassesStable
    program .r1 loop Relevant observe bodyPaths closure K hsound hstep hstable hobs

example : ∀ s o,
    VexModelDenotesObs Relevant observe
      (lowerPathFamilySummaries (branchingLoopWitness bodyPaths K)) s o ↔
      (whileLoopRegionSpec program .r1 loop Relevant observe).DenotesObs s o := by
  exact extractedModel_of_witnessComplete
    (LoopRegion (whileLoopRegionSpec program .r1 loop Relevant observe))
    (branchingLoopWitness bodyPaths K)
    (whileBranchingLoopWitnessComplete_of_branchClassesStable
      program .r1 loop Relevant observe bodyPaths closure K hsound hstep hstable hobs)

end Instances.Examples.Phase5Capstone
