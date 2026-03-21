import SymExec.Quotient
import SymExec.Bisimulation

/-!
# Semantic Closure Refinement

This file provides a semantic-closure variant of the explicit-closure quotient
pipeline from `SymExec/Quotient.lean`.

Instead of requiring syntactic closure:
`pc_lift b.sub φ ∈ closure`,
we require only that lifted PCs are determined by the quotient induced by
`closure`. This is the notion needed for symbolic PC languages whose lifted
syntax may grow without bound even when the semantic partition has stabilized.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

section SemanticClosure

variable {Sub PC State : Type*} [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Semantic closure: every lifted PC is constant on each `pcSetoidWith` class.

This is weaker than syntactic closure. It asks only that, for every model
branch `b` and every base PC `φ ∈ closure`, the predicate
`pc_lift b.sub φ` is determined by the quotient induced by `closure`. -/
def SemClosed (model : Finset (Branch Sub PC)) (closure : Finset PC) : Prop :=
  ∀ b ∈ model, ∀ φ ∈ closure, ∀ s₁ s₂ : State,
    ((pcSetoidWith isa closure).r s₁ s₂) →
      (isa.satisfies s₁ (isa.pc_lift b.sub φ) ↔
       isa.satisfies s₂ (isa.pc_lift b.sub φ))

/-- Ordinary syntactic closure implies semantic closure. -/
theorem semClosed_of_syntacticallyClosed
    (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (h_closed : ∀ b ∈ model, ∀ φ ∈ closure, isa.pc_lift b.sub φ ∈ closure) :
    SemClosed isa model closure := by
  intro b hb φ hφ s₁ s₂ h_equiv
  exact h_equiv (isa.pc_lift b.sub φ) (h_closed b hb φ hφ)

/-- Semantic closure is exactly what is needed to transport quotient
equivalence through branch execution. -/
theorem pcEquiv_eval_sub_semClosed
    {model : Finset (Branch Sub PC)} {closure : Finset PC}
    {s₁ s₂ : State} {b : Branch Sub PC}
    (hb : b ∈ model)
    (h_semClosed : SemClosed isa model closure)
    (h_equiv : (pcSetoidWith isa closure).r s₁ s₂) :
    (pcSetoidWith isa closure).r (isa.eval_sub b.sub s₁) (isa.eval_sub b.sub s₂) := by
  intro φ hφ
  constructor
  · intro h
    have h_lift₁ : isa.satisfies s₁ (isa.pc_lift b.sub φ) :=
      (isa.sat_lift s₁ b.sub φ).mpr h
    have h_lift₂ : isa.satisfies s₂ (isa.pc_lift b.sub φ) :=
      (h_semClosed b hb φ hφ s₁ s₂ h_equiv).mp h_lift₁
    exact (isa.sat_lift s₂ b.sub φ).mp h_lift₂
  · intro h
    have h_lift₂ : isa.satisfies s₂ (isa.pc_lift b.sub φ) :=
      (isa.sat_lift s₂ b.sub φ).mpr h
    have h_lift₁ : isa.satisfies s₁ (isa.pc_lift b.sub φ) :=
      (h_semClosed b hb φ hφ s₁ s₂ h_equiv).mpr h_lift₂
    exact (isa.sat_lift s₁ b.sub φ).mp h_lift₁

end SemanticClosure


section AbstractSystemSem

variable {Sub PC State : Type*} [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Backward direction using semantic closure instead of syntactic closure. -/
theorem quotient_backwardSem
    (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (h_contains : ∀ b ∈ model, b.pc ∈ closure)
    (h_semClosed : SemClosed isa model closure)
    (behavior : State → State → Prop)
    (h_sound : BranchModel.Sound isa (↑model : Set (Branch Sub PC)) behavior)
    (s : State) (a' : Quotient (pcSetoidWith isa closure))
    (h : abstractBehaviorWith isa model closure
      (Quotient.mk (pcSetoidWith isa closure) s) a') :
    ∃ s', behavior s s' ∧ Quotient.mk (pcSetoidWith isa closure) s' = a' := by
  obtain ⟨s₁, s₂, h_eq1, h_eq2, b, hb, hsat1, heval⟩ := h
  have h_equiv : (pcSetoidWith isa closure).r s s₁ :=
    Quotient.exact h_eq1.symm
  have h_fires_s : isa.satisfies s b.pc :=
    pcEquiv_branch_firesWith isa (h_contains b (Finset.mem_coe.mp hb))
      (pcEquiv_symm isa h_equiv) hsat1
  have h_beh : behavior s (isa.eval_sub b.sub s) :=
    h_sound b hb s h_fires_s
  have h_succ_equiv : (pcSetoidWith isa closure).r
      (isa.eval_sub b.sub s) (isa.eval_sub b.sub s₁) :=
    pcEquiv_eval_sub_semClosed isa (b := b) (hb := Finset.mem_coe.mp hb)
      h_semClosed h_equiv
  refine ⟨isa.eval_sub b.sub s, h_beh, ?_⟩
  rw [← h_eq2]
  apply Quotient.sound
  show (pcSetoidWith isa closure).r (isa.eval_sub b.sub s) s₂
  rw [← heval]
  exact h_succ_equiv

/-- The quotient map is a cross-system bisimulation under semantic closure. -/
theorem quotient_bisimulationSem
    (model : Finset (Branch Sub PC)) (closure : Finset PC)
    (h_contains : ∀ b ∈ model, b.pc ∈ closure)
    (h_semClosed : SemClosed isa model closure)
    (behavior : State → State → Prop)
    (h_sound : BranchModel.Sound isa (↑model : Set (Branch Sub PC)) behavior)
    (h_complete : BranchModel.Complete isa (↑model : Set (Branch Sub PC)) behavior) :
    CrossBisimulation
      (Quotient.mk (pcSetoidWith isa closure))
      behavior
      (abstractBehaviorWith isa model closure) where
  forward := quotient_forwardWith isa model closure behavior h_complete
  backward := quotient_backwardSem isa model closure h_contains h_semClosed behavior h_sound

end AbstractSystemSem


section EndToEndSem

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]

/-- End-to-end with semantic closure: oracle convergence yields a finite quotient
    bisimulation over a chosen closure without requiring syntactic `h_closed`. -/
theorem quotientBisimulationSem
    (oracle : BranchOracle Sub PC State)
    [h_dec : ∀ (s : State) (φ : PC), Decidable (oracle.isa.satisfies s φ)]
    (target : Finset (Branch Sub PC))
    (closure : Finset PC)
    (h_contains : ∀ b ∈ target, b.pc ∈ closure)
    (h_semClosed : SemClosed oracle.isa target closure)
    (h_productive : oracle.Productive target)
    (h_bounded : oracle.TargetBounded target)
    (h_target_complete : BranchModel.Complete oracle.isa
      (↑target : Set (Branch Sub PC)) oracle.behavior) :
    ∃ n, n ≤ target.card ∧
      CrossBisimulation
        (Quotient.mk (pcSetoidWith oracle.isa closure))
        oracle.behavior
        (abstractBehaviorWith oracle.isa (oracleSequence oracle n) closure) ∧
      Fintype.card (Quotient (pcSetoidWith oracle.isa closure)) ≤
        2 ^ closure.card := by
  obtain ⟨n, h_le, h_sound, h_complete⟩ :=
    branchAccumulation_sound_and_complete oracle target h_productive h_bounded h_target_complete
  have h_sub := oracleSequence_bounded oracle target h_bounded n
  have h_contains_n : ∀ b ∈ oracleSequence oracle n, b.pc ∈ closure := by
    intro b hb
    exact h_contains b (h_sub hb)
  have h_semClosed_n : SemClosed oracle.isa (oracleSequence oracle n) closure := by
    intro b hb φ hφ s₁ s₂ h_equiv
    exact h_semClosed b (h_sub hb) φ hφ s₁ s₂ h_equiv
  exact ⟨n, h_le,
    quotient_bisimulationSem oracle.isa (oracleSequence oracle n) closure
      h_contains_n h_semClosed_n oracle.behavior h_sound h_complete,
    abstractStateWith_card_bound oracle.isa closure⟩

end EndToEndSem
