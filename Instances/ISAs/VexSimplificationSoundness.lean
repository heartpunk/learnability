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
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1; bv_decide

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

private theorem uint64_and_max (x : UInt64) : x &&& 0xFFFF_FFFF_FFFF_FFFF = x := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1; bv_decide

private theorem uint64_max_and (x : UInt64) : 0xFFFF_FFFF_FFFF_FFFF &&& x = x := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1; bv_decide

private theorem uint64_and_zero (x : UInt64) : x &&& 0 = 0 := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1; bv_decide

private theorem uint64_zero_and (x : UInt64) : 0 &&& x = 0 := by
  show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1; bv_decide

theorem foldAnd64_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (a b : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (foldAnd64 a b) = evalSymExpr s a &&& evalSymExpr s b := by
  simp only [foldAnd64]
  split
  · simp only [evalSymExpr]                    -- const &&& const
  · rename_i x m                               -- x &&& const m
    simp only [evalSymExpr]
    split
    · next h => simp_all [uint64_and_max]
    · split
      · next h _ =>
        -- h should tell us m == 0; let's see the full error
        simp_all
      · rfl
  · rename_i m x                               -- const m &&& x
    simp only [evalSymExpr]
    split
    · next h => simp_all [uint64_max_and]
    · split
      · next h _ => simp_all
      · rfl
  · simp only [evalSymExpr]

private theorem uint64_add_left_cancel (R a b : UInt64) (h : R + a = R + b) : a = b := by
  have hbv : R.toBitVec + a.toBitVec = R.toBitVec + b.toBitVec :=
    congrArg UInt64.toBitVec h
  have hab : a.toBitVec = b.toBitVec := by bv_omega
  exact congrArg UInt64.ofBitVec hab

/-- Offset-based byte-range non-overlap for R+c1 vs R+c2.
    ByteMem operations are defined byte-by-byte via individual address lookups,
    not via contiguous range checks. Two byte sets {R+c1+i | i<sw} and
    {R+c2+j | j<lw} are disjoint when the offset ranges [c1,c1+sw) and
    [c2,c2+lw) don't overlap (mod 2^64 arithmetic preserves distances).

    This is stated directly as a ByteMem read/write property rather than
    going through ByteMem_read_write_nonoverlap (which requires absolute
    non-wrapping guards that don't hold after adding R). -/
private theorem ByteMem_read_write_nonoverlap_offset
    (lw sw : Width) (M : ByteMem) (R c1 v c2 : UInt64)
    (h1 : c1.toNat + sw.byteCount ≤ UInt64.size)
    (h2 : c2.toNat + lw.byteCount ≤ UInt64.size)
    (h3 : c1.toNat + sw.byteCount ≤ c2.toNat ∨ c2.toNat + lw.byteCount ≤ c1.toNat) :
    ByteMem.read lw (ByteMem.write sw M (R + c1) v) (R + c2) = ByteMem.read lw M (R + c2) := by
  have hp : ∀ i j, i < sw.byteCount → j < lw.byteCount →
      (R + c1) + UInt64.ofNat i ≠ (R + c2) + UInt64.ofNat j := by
    intro i j hi hj hcontra
    -- (R + c1) + i = (R + c2) + j
    -- By UInt64 associativity: R + (c1 + i) = R + (c2 + j)
    have hassoc1 : (R + c1) + UInt64.ofNat i = R + (c1 + UInt64.ofNat i) := UInt64.add_assoc ..
    have hassoc2 : (R + c2) + UInt64.ofNat j = R + (c2 + UInt64.ofNat j) := UInt64.add_assoc ..
    rw [hassoc1, hassoc2] at hcontra
    have hcancel := uint64_add_left_cancel R _ _ hcontra
    have h_ne : c1.toNat + i ≠ c2.toNat + j := by omega
    apply h_ne
    have h_i_small : i < UInt64.size := by omega
    have h_j_small : j < UInt64.size := by omega
    have h_ofNat_i : (UInt64.ofNat i).toNat = i := Nat.mod_eq_of_lt h_i_small
    have h_ofNat_j : (UInt64.ofNat j).toNat = j := Nat.mod_eq_of_lt h_j_small
    have h_ci_lt : c1.toNat + i < UInt64.size := by omega
    have h_cj_lt : c2.toNat + j < UInt64.size := by omega
    have := congrArg UInt64.toNat hcancel
    simp only [UInt64.toNat_add, h_ofNat_i, h_ofNat_j,
               Nat.mod_eq_of_lt h_ci_lt, Nat.mod_eq_of_lt h_cj_lt] at this
    omega
  cases lw <;> cases sw <;>
    simp only [ByteMem.read, ByteMem.write, Width.byteCount,
               ByteMem.read8, ByteMem.read16le, ByteMem.read32le, ByteMem.read64le,
               ByteMem.write8, ByteMem.write16le, ByteMem.write32le, ByteMem.write64le] at *
  all_goals first
    | exact readLEAux_writeLEAux_nonoverlap M _ v _ _ _ hp
    | (congr 1; congr 1
       exact readByte_writeLEAux_nonoverlap M _ v _ _
        (fun i hi => by simpa using hp i 0 hi (by omega)))
    | exact readLEAux_writeByte_nonoverlap M _ _ _ _
        (fun j hj => by simpa using hp 0 j (by omega) hj)
    | (congr 1; congr 1
       exact readByte_writeByte_ne M _ _ _ (by simpa using hp 0 0 (by omega) (by omega)))

/-- Same as above but for R - c1 vs R - c2 (sub64 pattern). -/
private theorem ByteMem_read_write_nonoverlap_sub_sub
    (lw sw : Width) (M : ByteMem) (R c1 v c2 : UInt64)
    (h1 : ((0 : UInt64) - c1).toNat + sw.byteCount ≤ UInt64.size)
    (h2 : ((0 : UInt64) - c2).toNat + lw.byteCount ≤ UInt64.size)
    (h3 : ((0 : UInt64) - c1).toNat + sw.byteCount ≤ ((0 : UInt64) - c2).toNat ∨
           ((0 : UInt64) - c2).toNat + lw.byteCount ≤ ((0 : UInt64) - c1).toNat) :
    ByteMem.read lw (ByteMem.write sw M (R - c1) v) (R - c2) = ByteMem.read lw M (R - c2) := by
  have hsub : ∀ (a b : UInt64), a - b = a + (0 - b) := by
    intro a b; show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
    simp [BitVec.sub_eq_add_neg]
  rw [hsub R c1, hsub R c2]
  exact ByteMem_read_write_nonoverlap_offset lw sw M R (0 - c1) v (0 - c2) h1 h2 h3

/-- R + c1 vs R - c2 (add64/sub64 mixed pattern). -/
private theorem ByteMem_read_write_nonoverlap_add_sub
    (lw sw : Width) (M : ByteMem) (R c1 v c2 : UInt64)
    (h1 : c1.toNat + sw.byteCount ≤ UInt64.size)
    (h2 : ((0 : UInt64) - c2).toNat + lw.byteCount ≤ UInt64.size)
    (h3 : c1.toNat + sw.byteCount ≤ ((0 : UInt64) - c2).toNat ∨
           ((0 : UInt64) - c2).toNat + lw.byteCount ≤ c1.toNat) :
    ByteMem.read lw (ByteMem.write sw M (R + c1) v) (R - c2) = ByteMem.read lw M (R - c2) := by
  have hsub : ∀ (a b : UInt64), a - b = a + (0 - b) := by
    intro a b; show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
    simp [BitVec.sub_eq_add_neg]
  rw [hsub R c2]
  exact ByteMem_read_write_nonoverlap_offset lw sw M R c1 v (0 - c2) h1 h2 h3

/-- R - c1 vs R + c2 (sub64/add64 mixed pattern). -/
private theorem ByteMem_read_write_nonoverlap_sub_add
    (lw sw : Width) (M : ByteMem) (R c1 v c2 : UInt64)
    (h1 : ((0 : UInt64) - c1).toNat + sw.byteCount ≤ UInt64.size)
    (h2 : c2.toNat + lw.byteCount ≤ UInt64.size)
    (h3 : ((0 : UInt64) - c1).toNat + sw.byteCount ≤ c2.toNat ∨
           c2.toNat + lw.byteCount ≤ ((0 : UInt64) - c1).toNat) :
    ByteMem.read lw (ByteMem.write sw M (R - c1) v) (R + c2) = ByteMem.read lw M (R + c2) := by
  have hsub : ∀ (a b : UInt64), a - b = a + (0 - b) := by
    intro a b; show UInt64.ofBitVec _ = UInt64.ofBitVec _; congr 1
    simp [BitVec.sub_eq_add_neg]
  rw [hsub R c1]
  exact ByteMem_read_write_nonoverlap_offset lw sw M R (0 - c1) v c2 h1 h2 h3

/-! ## resolveLoadFrom soundness

`resolveLoadFrom` resolves loads through store chains. Proved using:
- `ByteMem_read_write_same`: byte round-trip at same address/width
- `ByteMem_read_write_nonoverlap`: skip stores at non-overlapping byte ranges -/

theorem resolveLoadFrom_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (w : Width) (mem : SymMem Reg) (addr : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (resolveLoadFrom w mem addr) =
    ByteMem.read w (evalSymMem s mem) (evalSymExpr s addr) := by
  cases mem with
  | base => rfl
  | store sw innerMem sa sv =>
    have ih := resolveLoadFrom_sound w innerMem addr s
    simp only [resolveLoadFrom]
    split
    · -- Matching case
      rename_i hmatch
      have hw := (Bool.and_eq_true _ _).mp hmatch
      have hwEq : w = sw := eq_of_beq hw.1
      have haEq : addr = sa := eq_of_beq hw.2
      subst hwEq; subst haEq
      simp only [evalSymExpr, evalSymMem]
      rw [ByteMem_read_write_same]; simp only [truncate]
    · -- Non-matching: split on address patterns
      split
      · -- const/const
        rename_i a b heq
        have hsa : sa = SymExpr.const a := congrArg Prod.fst heq
        have haddr : addr = SymExpr.const b := congrArg Prod.snd heq
        subst hsa; subst haddr
        split
        · -- non-overlapping
          rename_i hnoverlap
          -- hnoverlap : rawConstRangesNonOverlapping ... = true
          -- Let's see what simp_all can do
          rw [ih]; simp only [evalSymExpr, evalSymMem]
          simp only [rawConstRangesNonOverlapping, decide_eq_true_eq] at hnoverlap
          exact (ByteMem_read_write_nonoverlap w sw _ _ _ _ hnoverlap.1 hnoverlap.2.1 hnoverlap.2.2).symm
        · simp only [evalSymExpr, evalSymMem]
      -- reg+const cases: split on the if, false branch is conservative
      -- catch-all (no if) is rfl
      · split
        · -- add64/add64 if-true: r1==r2 && offsets non-overlapping
          rename_i r1 c1 r2 c2 heq hif
          have hsa := congrArg Prod.fst heq; have haddr := congrArg Prod.snd heq
          subst hsa; subst haddr
          simp only [Bool.and_eq_true] at hif; obtain ⟨hr, hno⟩ := hif
          have := eq_of_beq hr; subst this
          simp only [rawConstRangesNonOverlapping, decide_eq_true_eq] at hno
          rw [ih]; simp only [evalSymExpr, evalSymMem]
          exact (ByteMem_read_write_nonoverlap_offset w sw _ (evalSymExpr s r1) c1 _ c2
            hno.1 hno.2.1 hno.2.2).symm
        · simp only [evalSymExpr, evalSymMem]
      · split
        · -- sub64/sub64 if-true
          rename_i r1 c1 r2 c2 heq hif
          have hsa := congrArg Prod.fst heq; have haddr := congrArg Prod.snd heq
          subst hsa; subst haddr
          simp only [Bool.and_eq_true] at hif; obtain ⟨hr, hno⟩ := hif
          have := eq_of_beq hr; subst this
          simp only [rawConstRangesNonOverlapping, decide_eq_true_eq] at hno
          rw [ih]; simp only [evalSymExpr, evalSymMem]
          exact (ByteMem_read_write_nonoverlap_sub_sub w sw _ (evalSymExpr s r1) c1 _ c2
            hno.1 hno.2.1 hno.2.2).symm
        · simp only [evalSymExpr, evalSymMem]
      · split
        · -- add64/sub64 if-true
          rename_i r1 c1 r2 c2 heq hif
          have hsa := congrArg Prod.fst heq; have haddr := congrArg Prod.snd heq
          subst hsa; subst haddr
          simp only [Bool.and_eq_true] at hif; obtain ⟨hr, hno⟩ := hif
          have := eq_of_beq hr; subst this
          simp only [rawConstRangesNonOverlapping, decide_eq_true_eq] at hno
          rw [ih]; simp only [evalSymExpr, evalSymMem]
          exact (ByteMem_read_write_nonoverlap_add_sub w sw _ (evalSymExpr s r1) c1 _ c2
            hno.1 hno.2.1 hno.2.2).symm
        · simp only [evalSymExpr, evalSymMem]
      · split
        · -- sub64/add64 if-true
          rename_i r1 c1 r2 c2 heq hif
          have hsa := congrArg Prod.fst heq; have haddr := congrArg Prod.snd heq
          subst hsa; subst haddr
          simp only [Bool.and_eq_true] at hif; obtain ⟨hr, hno⟩ := hif
          have := eq_of_beq hr; subst this
          simp only [rawConstRangesNonOverlapping, decide_eq_true_eq] at hno
          rw [ih]; simp only [evalSymExpr, evalSymMem]
          exact (ByteMem_read_write_nonoverlap_sub_add w sw _ (evalSymExpr s r1) c1 _ c2
            hno.1 hno.2.1 hno.2.2).symm
        · simp only [evalSymExpr, evalSymMem]
      · rfl

/-! ## Proved: simplifyLoadStoreExpr / simplifyLoadStoreMem soundness

Mutual structural induction using `foldAdd64_sound`, `foldSub64_sound`,
and `resolveLoadFrom_sound` as building blocks. -/

mutual
/-- `simplifyLoadStoreExpr` preserves expression evaluation. -/
theorem simplifyLoadStoreExpr_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (e : SymExpr Reg) (s : ConcreteState Reg) :
    evalSymExpr s (simplifyLoadStoreExpr e) = evalSymExpr s e := by
  match e with
  | .const _ | .reg _ => rfl
  | .low32 x => simp only [simplifyLoadStoreExpr, evalSymExpr]; rw [simplifyLoadStoreExpr_sound x s]
  | .uext32 x => simp only [simplifyLoadStoreExpr, evalSymExpr]; rw [simplifyLoadStoreExpr_sound x s]
  | .sext8to32 x => simp only [simplifyLoadStoreExpr, evalSymExpr]; rw [simplifyLoadStoreExpr_sound x s]
  | .sext32to64 x => simp only [simplifyLoadStoreExpr, evalSymExpr]; rw [simplifyLoadStoreExpr_sound x s]
  | .not64 x => simp only [simplifyLoadStoreExpr, evalSymExpr]; rw [simplifyLoadStoreExpr_sound x s]
  | .not32 x => simp only [simplifyLoadStoreExpr, evalSymExpr]; rw [simplifyLoadStoreExpr_sound x s]
  | .ite c t f =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound c s, simplifyLoadStoreExpr_sound t s, simplifyLoadStoreExpr_sound f s]
  | .sub32 a b | .and32 a b | .shl32 a b | .or32 a b | .xor32 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .add64 a b =>
    simp only [simplifyLoadStoreExpr]; rw [foldAdd64_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .sub64 a b =>
    simp only [simplifyLoadStoreExpr]; rw [foldSub64_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .and64 a b =>
    simp only [simplifyLoadStoreExpr]; rw [foldAnd64_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .xor64 a b | .or64 a b | .shl64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .shr64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .mul64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .mul32 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .sar64 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .sar32 a b =>
    simp only [simplifyLoadStoreExpr, evalSymExpr]
    rw [simplifyLoadStoreExpr_sound a s, simplifyLoadStoreExpr_sound b s]
  | .load w mem addr =>
    simp only [simplifyLoadStoreExpr]
    rw [resolveLoadFrom_sound]; simp only [evalSymExpr]
    rw [simplifyLoadStoreMem_sound mem s, simplifyLoadStoreExpr_sound addr s]

/-- `simplifyLoadStoreMem` preserves memory evaluation. -/
theorem simplifyLoadStoreMem_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (m : SymMem Reg) (s : ConcreteState Reg) :
    evalSymMem s (simplifyLoadStoreMem m) = evalSymMem s m := by
  match m with
  | .base => rfl
  | .store w mem addr val =>
    simp only [simplifyLoadStoreMem]
    split
    · -- inner mem simplified to .store: dead store elimination check
      rename_i w' innerMem storeAddr' _
      split
      · -- dead store eliminated
        simp only [evalSymMem]
        rw [simplifyLoadStoreExpr_sound addr s, simplifyLoadStoreExpr_sound val s]
        rename_i heq hif
        have ih := simplifyLoadStoreMem_sound mem s
        rw [heq] at ih; simp only [evalSymMem] at ih
        simp only [Bool.and_eq_true] at hif
        have hw := eq_of_beq hif.1; have ha := eq_of_beq hif.2
        subst hw; rw [← ha, simplifyLoadStoreExpr_sound addr s] at ih
        rw [← ih]
        -- Goal per width: writeX M' a v2 = writeX (writeX M' a v1) a v2
        cases w <;> simp only [ByteMem.write, ByteMem.write8, ByteMem.write16le,
          ByteMem.write32le, ByteMem.write64le]
        · exact (writeByte_writeByte_same _ _ _ _).symm
        all_goals exact (writeLEAux_writeLEAux_same _ _ _ _ _ (by simp [UInt64.size])).symm
      · -- no dead store
        simp only [evalSymMem]
        rw [simplifyLoadStoreMem_sound mem s,
            simplifyLoadStoreExpr_sound addr s,
            simplifyLoadStoreExpr_sound val s]
    · -- inner mem simplified to .base or other
      simp only [evalSymMem]
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
