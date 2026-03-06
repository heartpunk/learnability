import Bisimulation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Quotient Bisimulation

Extracts a finite abstract transition system from a complete branch model,
proved bisimilar to the concrete system. This is the publishable result of
Phase 4: "we extracted a finite abstract model."

## Construction

Given a sound and complete branch model `{b₁, ..., bₙ}`:

1. **PC closure**: close the model's PCs under `pc_lift bᵢ.sub (-)`.
   Semantically finite when `PC` is finite — bounded by `Fintype.card PC`.

2. **PC-equivalence**: `s ≈ s'` iff for all `φ ∈ PCClosure`,
   `satisfies s φ ↔ satisfies s' φ`.

3. **Congruence**: if `s ≈ s'` and branch b fires from s, then b fires
   from s' and successors are equivalent. Uses `sat_lift` + closure property.

4. **Abstract transitions**: defined existentially via representatives
   (avoiding `Quotient.lift₂`).

5. **Cross-system bisimulation**: quotient map is a bisimulation.

6. **Finiteness**: abstract states ≤ `2^|PCClosure|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-! ## Step 4a: PC Closure Construction

The PC closure is the smallest set containing all model PCs and closed
under `pc_lift bᵢ.sub (-)` for all branches in the model.

Computed by iterating `pcClosureStep` from `pcClosureBase` until fixpoint.
Terminates because `Finset PC` is bounded by `Finset.univ` when `[Fintype PC]`. -/

section PCClosure

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
  (isa : SymbolicISA Sub PC State)

/-- One round of closure: add all lifts of current PCs through all branch subs. -/
def pcClosureStep (model : Finset (Branch Sub PC)) (current : Finset PC) : Finset PC :=
  current ∪ model.biUnion (fun b => current.image (isa.pc_lift b.sub))

/-- Starting set: the PCs appearing in the model. -/
def pcClosureBase (model : Finset (Branch Sub PC)) : Finset PC :=
  model.image (fun b => b.pc)

/-- Iterate closure step n times from the base. -/
def pcClosureSeq (model : Finset (Branch Sub PC)) (n : ℕ) : Finset PC :=
  (pcClosureStep isa model)^[n] (pcClosureBase model)

set_option linter.unusedSectionVars false in
/-- `pcClosureStep` is monotone: current ⊆ pcClosureStep current. -/
theorem pcClosureStep_mono (model : Finset (Branch Sub PC)) (current : Finset PC) :
    current ⊆ pcClosureStep isa model current :=
  Finset.subset_union_left

set_option linter.unusedSectionVars false in
/-- The closure sequence is monotone. -/
theorem pcClosureSeq_mono (model : Finset (Branch Sub PC)) :
    ∀ n, pcClosureSeq isa model n ⊆ pcClosureSeq isa model (n + 1) := by
  intro n
  show (pcClosureStep isa model)^[n] (pcClosureBase model) ⊆
       (pcClosureStep isa model)^[n + 1] (pcClosureBase model)
  rw [Function.iterate_succ_apply']
  exact pcClosureStep_mono isa model _

/-- The closure sequence is bounded by `Finset.univ`. -/
theorem pcClosureSeq_bounded (model : Finset (Branch Sub PC)) :
    ∀ n, pcClosureSeq isa model n ⊆ (Finset.univ : Finset PC) :=
  fun _ => Finset.subset_univ _

/-- The closure sequence stabilizes within `Fintype.card PC` steps. -/
theorem pcClosureSeq_stabilizes (model : Finset (Branch Sub PC)) :
    ∃ n, n ≤ (Finset.univ : Finset PC).card ∧
      pcClosureSeq isa model n = pcClosureSeq isa model (n + 1) :=
  Finset.bounded_monotone_stabilizes_within
    (pcClosureSeq isa model) (Finset.univ : Finset PC)
    (pcClosureSeq_mono isa model)
    (pcClosureSeq_bounded isa model)

/-- The PC closure: the fixpoint of `pcClosureStep` applied to model PCs. -/
noncomputable def pcClosure (model : Finset (Branch Sub PC)) : Finset PC :=
  pcClosureSeq isa model (pcClosureSeq_stabilizes isa model).choose

/-- The closure is a fixpoint of `pcClosureStep`. -/
theorem pcClosure_fixpoint (model : Finset (Branch Sub PC)) :
    pcClosureStep isa model (pcClosure isa model) = pcClosure isa model := by
  have h_fix := (pcClosureSeq_stabilizes isa model).choose_spec.2
  unfold pcClosure pcClosureSeq at h_fix ⊢
  rw [Function.iterate_succ_apply'] at h_fix
  exact h_fix.symm

/-- Closure property: for any branch in the model and any PC in the closure,
    the lifted PC is also in the closure. -/
theorem pcClosure_closed (model : Finset (Branch Sub PC))
    (b : Branch Sub PC) (hb : b ∈ model)
    (φ : PC) (hφ : φ ∈ pcClosure isa model) :
    isa.pc_lift b.sub φ ∈ pcClosure isa model := by
  have h_fix := pcClosure_fixpoint isa model
  rw [← h_fix]
  unfold pcClosureStep
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨b, hb, Finset.mem_image_of_mem _ hφ⟩

/-- The base PCs are contained in every step of the sequence. -/
theorem pcClosureBase_sub_seq (model : Finset (Branch Sub PC)) :
    ∀ n, pcClosureBase model ⊆ pcClosureSeq isa model n := by
  intro n
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact Finset.Subset.trans ih (pcClosureSeq_mono isa model n)

/-- The closure contains all model PCs. -/
theorem pcClosure_contains_model_pcs (model : Finset (Branch Sub PC))
    (b : Branch Sub PC) (hb : b ∈ model) :
    b.pc ∈ pcClosure isa model := by
  unfold pcClosure
  exact pcClosureBase_sub_seq isa model _ (Finset.mem_image_of_mem _ hb)

end PCClosure


/-! ## Step 4b: PC-Equivalence and Congruence

Two states are PC-equivalent (w.r.t. the closure) when they satisfy exactly
the same PCs in the closure. This is an equivalence relation, and it's a
congruence: transitions respect it.

The congruence proof uses `sat_lift` + the closure property from Step 4a. -/

section PCEquiv

variable {Sub PC State : Type*} [DecidableEq PC] [Fintype PC]
  (isa : SymbolicISA Sub PC State)

/-- Two states are PC-equivalent w.r.t. a closure: they agree on all PCs in it. -/
def pcEquiv (closure : Finset PC) (s₁ s₂ : State) : Prop :=
  ∀ φ ∈ closure, isa.satisfies s₁ φ ↔ isa.satisfies s₂ φ

set_option linter.unusedSectionVars false in
theorem pcEquiv_refl (closure : Finset PC) (s : State) :
    pcEquiv isa closure s s :=
  fun _ _ => Iff.rfl

set_option linter.unusedSectionVars false in
theorem pcEquiv_symm {closure : Finset PC} {s₁ s₂ : State}
    (h : pcEquiv isa closure s₁ s₂) : pcEquiv isa closure s₂ s₁ :=
  fun φ hφ => (h φ hφ).symm

set_option linter.unusedSectionVars false in
theorem pcEquiv_trans {closure : Finset PC} {s₁ s₂ s₃ : State}
    (h₁₂ : pcEquiv isa closure s₁ s₂) (h₂₃ : pcEquiv isa closure s₂ s₃) :
    pcEquiv isa closure s₁ s₃ :=
  fun φ hφ => (h₁₂ φ hφ).trans (h₂₃ φ hφ)

/-- PC-equivalence over a model's closure as a `Setoid`. -/
def pcSetoid (model : Finset (Branch Sub PC)) : Setoid State where
  r := pcEquiv isa (pcClosure isa model)
  iseqv := {
    refl := pcEquiv_refl isa _
    symm := pcEquiv_symm isa
    trans := pcEquiv_trans isa
  }

/-- If two states are PC-equivalent (over the closure) and a branch in the
    model fires from one, it fires from the other. -/
theorem pcEquiv_branch_fires {model : Finset (Branch Sub PC)}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb : b ∈ model)
    (h_equiv : (pcSetoid isa model).r s₁ s₂)
    (h_fires : isa.satisfies s₁ b.pc) :
    isa.satisfies s₂ b.pc :=
  (h_equiv b.pc (pcClosure_contains_model_pcs isa model b hb)).mp h_fires

/-- If two states are PC-equivalent (over the closure), their successors
    under any branch in the model are also PC-equivalent.

    For any `φ ∈ closure`:
    `satisfies (eval_sub σ s₁) φ ↔ satisfies s₁ (pc_lift σ φ)` (by sat_lift)
    `↔ satisfies s₂ (pc_lift σ φ)` (by h_equiv, since pc_lift σ φ ∈ closure)
    `↔ satisfies (eval_sub σ s₂) φ` (by sat_lift). -/
theorem pcEquiv_eval_sub {model : Finset (Branch Sub PC)}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb : b ∈ model)
    (h_equiv : (pcSetoid isa model).r s₁ s₂) :
    (pcSetoid isa model).r (isa.eval_sub b.sub s₁) (isa.eval_sub b.sub s₂) := by
  intro φ hφ
  constructor
  · intro h
    rw [← isa.sat_lift s₂ b.sub φ]
    rw [← isa.sat_lift s₁ b.sub φ] at h
    exact (h_equiv (isa.pc_lift b.sub φ) (pcClosure_closed isa model b hb φ hφ)).mp h
  · intro h
    rw [← isa.sat_lift s₁ b.sub φ]
    rw [← isa.sat_lift s₂ b.sub φ] at h
    exact (h_equiv (isa.pc_lift b.sub φ) (pcClosure_closed isa model b hb φ hφ)).mpr h

end PCEquiv
