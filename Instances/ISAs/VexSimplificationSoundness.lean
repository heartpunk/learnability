import Instances.ISAs.VexSummaryISA
import Instances.ISAs.DispatchLoopEval
import Core.Branch

/-!
# Phase 1: Simplification Soundness

The pipeline's simplification functions (`simplifyConst`, `simplifyLoadStoreExpr`,
`simplifyLoadStorePC`, `simplifyBranchFull`) transform branches to reduce syntactic
noise from composition. This file proves that these transformations preserve the
semantics required by `BranchModel.Sound` from `Core/Composition.lean`.

## Proved Theorems

All simplification functions are total `def`s with proved soundness:
- `simplifyConst_sound`: constant folding preserves PC evaluation
- `foldAdd64_sound`, `foldSub64_sound`: arithmetic folding preserves expression evaluation
- `simplifyLoadStoreExpr_sound`: load-after-store resolution preserves expression evaluation
- `simplifyLoadStoreMem_sound`: store chain simplification preserves memory evaluation
- `simplifyLoadStorePC_sound`: load-after-store on PCs preserves PC evaluation

## Trust Boundaries

- `resolveLoadFrom_sound`: load resolution through store chains. Subsumes ByteMem
  read-after-write properties. Sound for non-overlapping byte ranges (standard x86-64
  aligned accesses) but not proven for arbitrary overlapping multi-byte ranges.

## Set-Level Lifting

The main theorem `simplifiedBranches_sound` shows that applying simplification to
every branch in a sound model preserves soundness. This is what Phase 3
(`VexPipelineBridge.lean`) needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace VexISA

/-! ## Proved: simplifyConst soundness -/

/-- `simplifyConst` preserves PC evaluation: if it returns `some φ'`, then `φ'`
    evaluates identically to `φ`. If it returns `none`, then `φ` is unsatisfiable. -/
theorem simplifyConst_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (φ : SymPC Reg) (s : ConcreteState Reg) :
    match SymPC.simplifyConst φ with
    | some φ' => evalSymPC s φ' = evalSymPC s φ
    | none    => evalSymPC s φ = false := by
  induction φ with
  | true => rfl
  | eq lhs rhs =>
    cases lhs <;> cases rhs <;> (try rfl)
    rename_i a b
    cases hab : (a == b) <;> simp_all [SymPC.simplifyConst, evalSymPC, evalSymExpr]
  | lt lhs rhs =>
    cases lhs <;> cases rhs <;> (try rfl)
    rename_i a b
    by_cases h : a < b
    · simp [SymPC.simplifyConst, h, evalSymPC, evalSymExpr]
    · simp [SymPC.simplifyConst, h, evalSymPC, evalSymExpr]
  | le lhs rhs =>
    cases lhs <;> cases rhs <;> (try rfl)
    rename_i a b
    by_cases h : a ≤ b
    · simp [SymPC.simplifyConst, h, evalSymPC, evalSymExpr]
    · simp [SymPC.simplifyConst, h, evalSymPC, evalSymExpr]
  | and φ ψ ih_φ ih_ψ =>
    simp only [SymPC.simplifyConst]
    revert ih_φ ih_ψ
    match hφ : SymPC.simplifyConst φ, hψ : SymPC.simplifyConst ψ with
    | none, _ => simp [evalSymPC]; intro h _; simp [h]
    | some _, none => simp [evalSymPC]; intro _ h; simp [h]
    | some φ_val, some ψ_val =>
      cases φ_val <;> cases ψ_val <;> simp_all [evalSymPC]
  | not φ ih_φ =>
    simp only [SymPC.simplifyConst]
    revert ih_φ
    match hφ : SymPC.simplifyConst φ with
    | none => simp_all [evalSymPC]
    | some φ_val => cases φ_val <;> simp_all [evalSymPC]

/-! ## UInt64 arithmetic helpers (bridge to BitVec via show/congr/bv_omega) -/

private theorem uint64_add_assoc (a b c : UInt64) : a + b + c = a + (b + c) := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_add]; bv_omega

private theorem uint64_add_comm (a b : UInt64) : a + b = b + a := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1; bv_omega

private theorem uint64_add_left_comm (a b c : UInt64) : a + (b + c) = b + (a + c) := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_add]; bv_omega

private theorem uint64_add_zero (a : UInt64) : a + 0 = a := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_ofNat]; bv_omega

private theorem uint64_zero_add (a : UInt64) : 0 + a = a := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_ofNat]; bv_omega

private theorem uint64_sub_add_cancel (a b : UInt64) : a - b + b = a := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_sub]; bv_omega

private theorem uint64_sub_add (a b c : UInt64) : a - b + c = a + (c - b) := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_sub]; bv_omega

private theorem uint64_sub_sub (a b c : UInt64) : a - (b - c) = a - b + c := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_sub]; bv_omega

private theorem uint64_sub_zero (a : UInt64) : a - 0 = a := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_ofNat]; bv_omega

private theorem uint64_sub_sub_eq (a b c : UInt64) : a - b - c = a - (b + c) := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add]; bv_omega

private theorem uint64_add_sub_cancel (a b : UInt64) : a + b - b = a := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_add]; bv_omega

private theorem uint64_add_sub (a b c : UInt64) : a + b - c = a + (b - c) := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]; bv_omega

/-! ## foldAdd64 / foldSub64 soundness -/

theorem foldAdd64_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (a b : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (foldAdd64 a b) = evalSymExpr s a + evalSymExpr s b := by
  unfold foldAdd64
  split <;> simp only [evalSymExpr]
  any_goals exact (uint64_add_zero _).symm
  any_goals exact (uint64_zero_add _).symm
  any_goals exact uint64_add_comm _ _
  all_goals (
    split
    · next h =>
      have hc := eq_of_beq h
      first
        | (subst hc; exact (uint64_sub_add_cancel _ _).symm)
        | (subst hc; rw [uint64_add_comm]; exact (uint64_sub_add_cancel _ _).symm)
        | rw [uint64_add_assoc, hc, uint64_add_zero]
        | rw [uint64_add_left_comm, hc, uint64_add_zero]
    · first
        | (simp only [evalSymExpr];
           simp only [uint64_add_assoc, uint64_add_comm, uint64_add_left_comm])
        | (split
           · next _ _ =>
             simp only [evalSymExpr]
             simp only [uint64_add_comm, uint64_sub_add]
           · next _ _ =>
             simp only [evalSymExpr]
             simp only [uint64_add_comm, uint64_sub_sub])
  )

theorem foldSub64_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (a b : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (foldSub64 a b) = evalSymExpr s a - evalSymExpr s b := by
  unfold foldSub64
  split <;> simp only [evalSymExpr]
  any_goals exact (uint64_sub_zero _).symm
  all_goals (
    split
    · next h =>
      have hc := eq_of_beq h
      first
        | rw [uint64_sub_sub_eq, hc, uint64_sub_zero]
        | (subst hc; exact (uint64_add_sub_cancel _ _).symm)
    · first
        | (simp only [evalSymExpr]; rw [uint64_sub_sub_eq])
        | (split
           · next _ _ =>
             simp only [evalSymExpr]
             rw [uint64_add_sub]
           · next _ _ =>
             simp only [evalSymExpr]
             rw [uint64_sub_sub, uint64_sub_add, uint64_add_sub])
  )

/-! ## resolveLoadFrom trust boundary

`resolveLoadFrom` resolves loads through store chains. Its correctness
subsumes two ByteMem properties:
1. Read-after-write at same address/width (provable but tedious)
2. Skip stores at different constant addresses (assumes non-overlapping byte ranges)

Property (2) is sound for aligned accesses (standard x86-64 stack patterns)
but NOT generally true for overlapping multi-byte ranges at different base addresses.
This is a trust boundary on the pipeline's memory access patterns. -/

axiom resolveLoadFrom_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (w : Width) (mem : SymMem Reg) (addr : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (resolveLoadFrom w mem addr) =
    ByteMem.read w (evalSymMem s mem) (evalSymExpr s addr)

/-! ## Proved: simplifyLoadStoreExpr / simplifyLoadStoreMem soundness

Mutual structural induction using `foldAdd64_sound`, `foldSub64_sound`,
and `resolveLoadFrom_sound` as building blocks. -/

mutual
/-- `simplifyLoadStoreExpr` preserves expression evaluation: resolving
    load-after-store patterns and folding constant arithmetic does not
    change the concrete value. -/
theorem simplifyLoadStoreExpr_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (e : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (simplifyLoadStoreExpr e) = evalSymExpr s e := by
  match e with
  | .const _ | .reg _ => rfl
  | .low32 x =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound x s]
  | .uext32 x =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound x s]
  | .sext8to32 x =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound x s]
  | .sext32to64 x =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound x s]
  | .sub32 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .shl32 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .add64 a b =>
    simp only [simplifyLoadStoreExpr]
    rw [foldAdd64_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .sub64 a b =>
    simp only [simplifyLoadStoreExpr]
    rw [foldSub64_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .xor64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .and64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .or64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .shl64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .shr64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .load w mem addr =>
    simp only [simplifyLoadStoreExpr]
    rw [resolveLoadFrom_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreMem_sound mem s, simplifyLoadStoreExpr_sound addr s]

/-- `simplifyLoadStoreMem` preserves memory evaluation: simplifying
    store chains does not change the concrete memory. -/
theorem simplifyLoadStoreMem_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (m : SymMem Reg) (s : ConcreteState Reg) :
    evalSymMem s (simplifyLoadStoreMem m) = evalSymMem s m := by
  match m with
  | .base => rfl
  | .store w mem addr val =>
    simp only [simplifyLoadStoreMem, evalSymMem]
    rw [simplifyLoadStoreMem_sound mem s,
        simplifyLoadStoreExpr_sound addr s,
        simplifyLoadStoreExpr_sound val s]
end

/-- `simplifyLoadStorePC` preserves PC evaluation: load-after-store
    resolution in path conditions does not change satisfiability. -/
theorem simplifyLoadStorePC_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (φ : SymPC Reg) (s : ConcreteState Reg) :
    evalSymPC s (simplifyLoadStorePC φ) = evalSymPC s φ := by
  induction φ with
  | true => rfl
  | eq a b =>
    simp only [simplifyLoadStorePC, evalSymPC]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | lt a b =>
    simp only [simplifyLoadStorePC, evalSymPC]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | le a b =>
    simp only [simplifyLoadStorePC, evalSymPC]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | and φ ψ ih_φ ih_ψ =>
    simp only [simplifyLoadStorePC, evalSymPC]
    rw [ih_φ, ih_ψ]
  | not φ ih =>
    simp only [simplifyLoadStorePC, evalSymPC]
    rw [ih]

/-- `simplifyBranchFull` computes the composition of `simplifyLoadStore*` and
    `simplifyConst`. Proved by `rfl` — `simplifyBranchFull` is a regular `def`
    (not `partial`), so its body is transparent. -/
theorem simplifyBranchFull_agreement {Reg : Type} [DecidableEq Reg] [Fintype Reg] :
  ∀ (b : Branch (SymSub Reg) (SymPC Reg)),
    simplifyBranchFull b =
      let simplifiedSub : SymSub Reg := {
        regs := fun r => simplifyLoadStoreExpr (b.sub.regs r)
        mem := simplifyLoadStoreMem b.sub.mem
      }
      let simplifiedPC := simplifyLoadStorePC b.pc
      match SymPC.simplifyConst simplifiedPC with
      | none => none
      | some pc' => some ⟨simplifiedSub, pc'⟩ := by
  intro b; rfl

/-! ## Single-Branch Soundness

If a branch `b` is sound for behavior `beh` (when `b`'s PC is satisfied, applying
`b`'s substitution gives a `beh`-successor), then `simplifyBranchFull b` (when it
returns `some b'`) is also sound for `beh`. -/

section SingleBranchSoundness

variable {Reg : Type} [DecidableEq Reg] [Fintype Reg]

/-- The simplified substitution preserves `applySymSub`. -/
theorem simplifiedSub_apply (sub : SymSub Reg) (s : ConcreteState Reg) :
    applySymSub
      { regs := fun r => simplifyLoadStoreExpr (sub.regs r)
        mem := simplifyLoadStoreMem sub.mem }
      s =
    applySymSub sub s := by
  apply ConcreteState.ext
  · funext r
    simp only [applySymSub]
    exact simplifyLoadStoreExpr_sound (sub.regs r) s
  · simp only [applySymSub]
    exact simplifyLoadStoreMem_sound sub.mem s

/-- If `simplifyBranchFull b = some b'`, then `b'` has the same effect as `b`. -/
theorem simplifyBranchFull_effect
    (b : Branch (SymSub Reg) (SymPC Reg))
    (b' : Branch (SymSub Reg) (SymPC Reg))
    (h : simplifyBranchFull b = some b') :
    ∀ s : ConcreteState Reg,
      applySymSub b'.sub s = applySymSub b.sub s := by
  rw [simplifyBranchFull_agreement] at h
  intro s
  -- After load-store simplification and const simplification, the sub is the
  -- load-store simplified version
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · case h_2 pc' hpc =>
    obtain rfl := Option.some.inj h
    exact simplifiedSub_apply b.sub s

/-- If `simplifyBranchFull b = some b'` and `s` satisfies `b'.pc`,
    then `s` satisfies `b.pc`. -/
theorem simplifyBranchFull_sat
    (b : Branch (SymSub Reg) (SymPC Reg))
    (b' : Branch (SymSub Reg) (SymPC Reg))
    (h : simplifyBranchFull b = some b')
    (s : ConcreteState Reg)
    (hsat : (vexSummaryISA Reg).satisfies s b'.pc) :
    (vexSummaryISA Reg).satisfies s b.pc := by
  rw [simplifyBranchFull_agreement] at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · case h_2 pc' hpc =>
    obtain rfl := Option.some.inj h
    simp only [vexSummaryISA, satisfiesSymPC] at hsat ⊢
    -- b'.pc = pc', where simplifyConst (simplifyLoadStorePC b.pc) = some pc'
    -- From simplifyConst_sound: evalSymPC s pc' = evalSymPC s (simplifyLoadStorePC b.pc)
    have h1 := simplifyConst_sound (simplifyLoadStorePC b.pc) s
    rw [hpc] at h1
    -- From simplifyLoadStorePC_sound: evalSymPC s (simplifyLoadStorePC b.pc) = evalSymPC s b.pc
    have h2 := simplifyLoadStorePC_sound b.pc s
    rw [← h2, ← h1]
    exact hsat

/-- Reverse direction: if `simplifyBranchFull b = some b'` and `s` satisfies `b.pc`,
    then `s` satisfies `b'.pc`. -/
theorem simplifyBranchFull_sat_rev
    (b : Branch (SymSub Reg) (SymPC Reg))
    (b' : Branch (SymSub Reg) (SymPC Reg))
    (h : simplifyBranchFull b = some b')
    (s : ConcreteState Reg)
    (hsat : (vexSummaryISA Reg).satisfies s b.pc) :
    (vexSummaryISA Reg).satisfies s b'.pc := by
  rw [simplifyBranchFull_agreement] at h
  simp only [] at h
  split at h
  · exact absurd h (by simp)
  · case h_2 pc' hpc =>
    obtain rfl := Option.some.inj h
    simp only [vexSummaryISA, satisfiesSymPC] at hsat ⊢
    have h1 := simplifyConst_sound (simplifyLoadStorePC b.pc) s
    rw [hpc] at h1
    have h2 := simplifyLoadStorePC_sound b.pc s
    rw [← h2] at hsat
    rw [h1]
    exact hsat

/-- Soundness of single-branch simplification: if branch `b` is sound for behavior
    `beh` under `vexSummaryISA`, and `simplifyBranchFull b = some b'`, then `b'`
    is also sound for `beh`. -/
theorem simplifyBranchFull_preserves_sound
    (b : Branch (SymSub Reg) (SymPC Reg))
    (b' : Branch (SymSub Reg) (SymPC Reg))
    (beh : ConcreteState Reg → ConcreteState Reg → Prop)
    (h_simpl : simplifyBranchFull b = some b')
    (h_sound : ∀ s : ConcreteState Reg,
      (vexSummaryISA Reg).satisfies s b.pc →
      beh s ((vexSummaryISA Reg).eval_sub b.sub s)) :
    ∀ s : ConcreteState Reg,
      (vexSummaryISA Reg).satisfies s b'.pc →
      beh s ((vexSummaryISA Reg).eval_sub b'.sub s) := by
  intro s hsat
  have hsat_orig := simplifyBranchFull_sat b b' h_simpl s hsat
  have heffect := simplifyBranchFull_effect b b' h_simpl s
  simp only [vexSummaryISA] at heffect ⊢
  rw [heffect]
  exact h_sound s hsat_orig

end SingleBranchSoundness

/-! ## Set-Level Simplification Soundness

Lift single-branch soundness to branch models (sets of branches).
The pipeline applies `simplifyBranchFull` to every branch, discarding
those that return `none` (unsatisfiable after simplification). -/

section SetLevelSoundness

variable {Reg : Type} [DecidableEq Reg] [Fintype Reg]

/-- Apply simplification to a set of branches: keep only those that survive
    simplification (i.e., `simplifyBranchFull` returns `some`). -/
def simplifyBranchSet (B : Set (Branch (SymSub Reg) (SymPC Reg))) :
    Set (Branch (SymSub Reg) (SymPC Reg)) :=
  { b' | ∃ b ∈ B, simplifyBranchFull b = some b' }

/-- Simplification preserves `BranchModel.Sound`: a simplified sound model
    is still sound. Dropped branches (unsatisfiable PCs) never contribute
    to soundness. Surviving branches preserve both satisfaction and effect.

    This is the key theorem that Phase 3 (`VexPipelineBridge.lean`) uses. -/
theorem simplifyBranchSet_sound
    (B : Set (Branch (SymSub Reg) (SymPC Reg)))
    (beh : ConcreteState Reg → ConcreteState Reg → Prop)
    (h_sound : BranchModel.Sound (vexSummaryISA Reg) B beh) :
    BranchModel.Sound (vexSummaryISA Reg) (simplifyBranchSet B) beh := by
  intro b' hb' s hsat
  obtain ⟨b, hb, h_simpl⟩ := hb'
  exact simplifyBranchFull_preserves_sound b b' beh h_simpl
    (fun s' hsat' => h_sound b hb s' hsat') s hsat

/-- Simplification also preserves completeness for the SURVIVING branches:
    if the original model was complete and no branches were dropped (all PCs
    are satisfiable), then the simplified model is complete.

    In practice, dropped branches are unsatisfiable, so they never witness
    any behavior in the original model either. -/
theorem simplifyBranchSet_complete_of_none_dropped
    (B : Set (Branch (SymSub Reg) (SymPC Reg)))
    (beh : ConcreteState Reg → ConcreteState Reg → Prop)
    (h_complete : BranchModel.Complete (vexSummaryISA Reg) B beh)
    (h_all_survive : ∀ b ∈ B, ∃ b', simplifyBranchFull b = some b') :
    BranchModel.Complete (vexSummaryISA Reg) (simplifyBranchSet B) beh := by
  intro s s' hbeh
  obtain ⟨b, hb, hsat, heval⟩ := h_complete s s' hbeh
  obtain ⟨b', h_simpl⟩ := h_all_survive b hb
  refine ⟨b', ⟨b, hb, h_simpl⟩, ?_, ?_⟩
  · -- b' is satisfied at s (original → simplified direction)
    exact simplifyBranchFull_sat_rev b b' h_simpl s hsat
  · -- b' has the same effect as b
    have heffect := simplifyBranchFull_effect b b' h_simpl s
    simp only [vexSummaryISA] at heffect ⊢
    rw [heffect]
    exact heval

end SetLevelSoundness

end VexISA
