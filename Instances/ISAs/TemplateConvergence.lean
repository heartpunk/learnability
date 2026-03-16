import Instances.ISAs.AntiUnify
import SymExec.Refinement

/-!
# Template Convergence

Connects template closure (from anti-unification) to semantic closure
(from SymExec/Refinement.lean), enabling quotient bisimulation WITHOUT
requiring syntactic PC closure.

## The problem

Ground PC closure explodes (7 → 59 → 475 → 3935 PCs per round) because
`pc_lift b.sub φ` (= `substSymPC b.sub φ` for VexISA) generates new
syntax. But the SEMANTIC partition stabilizes much earlier: only 23
branches with stable template structure.

## The solution

Template closure is closed BY CONSTRUCTION: holes are inert under
`substTemplatePC`, so applying a branch substitution to a template
gives a template (same shape, different hole value). The bridge theorem
(`substSymPC_instantiatePC`) connects this to ground-level `pc_lift`,
giving `SemClosed` via template equivalence.

## Key theorem

`templateClosed_preserves_lifted`: if template set Ψ is closed under
model substitutions, then template-equivalent states agree on all
lifted PCs of template instances.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-! ## Definitions -/

/-- Template set Ψ is closed under model: `substTemplatePC b.sub T ∈ Ψ`
    for all `b ∈ model`, `T ∈ Ψ`. This is the template analog of
    syntactic PC closure, but holds BY CONSTRUCTION since holes are
    inert under substitution. -/
def TemplateClosed {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (model : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (Ψ : Set (TemplatePC Reg)) : Prop :=
  ∀ b ∈ model, ∀ T ∈ Ψ, substTemplatePC b.sub T ∈ Ψ

/-- Every branch PC in the model is an instance of some template in Ψ. -/
def AllInstancesOf {Reg : Type}
    (model : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (Ψ : Set (TemplatePC Reg)) : Prop :=
  ∀ b ∈ model, ∃ T ∈ Ψ, ∃ v : HoleVal Reg, b.pc = instantiatePC v T

/-- Template equivalence: states agree on all instances of all templates in Ψ.
    This is an INFINITE relation (quantifies over all valuations), unlike
    `pcSetoidWith` which is finite (quantifies over a finite closure). -/
def TemplateEquiv {Reg : Type} {State : Type*}
    (Ψ : Set (TemplatePC Reg))
    (sat : State → SymPC Reg → Prop) (s₁ s₂ : State) : Prop :=
  ∀ T ∈ Ψ, ∀ v : HoleVal Reg, sat s₁ (instantiatePC v T) ↔ sat s₂ (instantiatePC v T)

/-! ## Core theorem: template closure preserves lifted PCs -/

/-- If Ψ is template-closed under model, then template-equivalent states
    agree on all lifted PCs of template instances.

    This is the key theorem: it shows that template closure gives the
    SEMANTIC consequence needed for bisimulation, even when syntactic
    closure (pc_lift b.sub φ ∈ closure) fails.

    Proof: substSymPC b.sub (instantiatePC v T)
         = instantiatePC v' (substTemplatePC b.sub T)    [bridge]
    where v' h = substSymExpr b.sub (v h), and substTemplatePC b.sub T ∈ Ψ
    by template closure, so template equivalence applies. -/
theorem templateClosed_preserves_lifted {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {State : Type*}
    (sat : State → SymPC Reg → Prop)
    (model : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (Ψ : Set (TemplatePC Reg))
    (h_closed : TemplateClosed model Ψ)
    (b : Branch (SymSub Reg) (SymPC Reg)) (hb : b ∈ model)
    (T : TemplatePC Reg) (hT : T ∈ Ψ)
    (v : HoleVal Reg) (s₁ s₂ : State)
    (h_equiv : TemplateEquiv Ψ sat s₁ s₂) :
    sat s₁ (substSymPC b.sub (instantiatePC v T)) ↔
    sat s₂ (substSymPC b.sub (instantiatePC v T)) := by
  -- substTemplatePC b.sub T ∈ Ψ by template closure
  have hT' : substTemplatePC b.sub T ∈ Ψ := h_closed b hb T hT
  -- Rewrite both sides using the bridge theorem
  rw [substSymPC_instantiatePC]
  -- Now the goal is about instantiatePC v' (substTemplatePC b.sub T)
  -- which is an instance of a template in Ψ, so TemplateEquiv applies
  exact h_equiv (substTemplatePC b.sub T) hT' (fun h => substSymExpr b.sub (v h))

/-! ## Matching preserved under substitution -/

/-- Substitution preserves MatchingPC structure: if two PCs have matching
    top-level constructors, so do their substituted versions. -/
theorem substSymPC_matchingPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (σ : SymSub Reg) (φ₁ φ₂ : SymPC Reg)
    (h : MatchingPC φ₁ φ₂) : MatchingPC (substSymPC σ φ₁) (substSymPC σ φ₂) := by
  match φ₁, φ₂ with
  | .true, .true => trivial
  | .eq _ _, .eq _ _ => trivial
  | .lt _ _, .lt _ _ => trivial
  | .le _ _, .le _ _ => trivial
  | .and a1 a2, .and b1 b2 =>
    simp [MatchingPC] at h ⊢
    exact ⟨substSymPC_matchingPC σ a1 b1 h.1, substSymPC_matchingPC σ a2 b2 h.2⟩
  | .not a, .not b =>
    simp [MatchingPC] at h ⊢
    exact substSymPC_matchingPC σ a b h
  | .true, .eq _ _ | .true, .lt _ _ | .true, .le _ _ | .true, .and _ _ | .true, .not _
  | .eq _ _, .true | .eq _ _, .lt _ _ | .eq _ _, .le _ _ | .eq _ _, .and _ _ | .eq _ _, .not _
  | .lt _ _, .true | .lt _ _, .eq _ _ | .lt _ _, .le _ _ | .lt _ _, .and _ _ | .lt _ _, .not _
  | .le _ _, .true | .le _ _, .eq _ _ | .le _ _, .lt _ _ | .le _ _, .and _ _ | .le _ _, .not _
  | .and _ _, .true | .and _ _, .eq _ _ | .and _ _, .lt _ _ | .and _ _, .le _ _ | .and _ _, .not _
  | .not _, .true | .not _, .eq _ _ | .not _, .lt _ _ | .not _, .le _ _ | .not _, .and _ _ =>
    simp [MatchingPC] at h

/-! ## Template closure → SemClosed

The connection from template-level reasoning to the existing proof chain.
`SemClosed` requires: for every b ∈ model, φ ∈ closure, if states agree
on closure PCs then they agree on `pc_lift b.sub φ`. Template closure
gives this when the closure PCs are instances of templates in Ψ and
pcSetoidWith-equivalence implies template equivalence. -/

/-- Template closure + coverage implies semantic closure.

    Hypotheses:
    - `h_tclosed`: Ψ is closed under model substitutions
    - `h_closure_inst`: every closure PC is a template instance
    - `h_pcSetoid_refines`: pcSetoidWith-equivalence implies template equivalence
      (the closure contains enough ground PCs to determine template truth values)

    The last hypothesis is the crux: it says the finite quotient induced by
    the closure is at least as fine as the infinite template quotient. This
    holds when the closure PCs span enough valuations of each template's holes
    to distinguish all template-inequivalent state pairs. -/
theorem semClosed_of_templateClosure {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {State : Type*}
    (isa : SymbolicISA (SymSub Reg) (SymPC Reg) State)
    (model : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (closure : Finset (SymPC Reg))
    (Ψ : Set (TemplatePC Reg))
    (h_tclosed : TemplateClosed model Ψ)
    (h_closure_inst : ∀ φ ∈ closure, ∃ T ∈ Ψ, ∃ v : HoleVal Reg, φ = instantiatePC v T)
    (h_pcSetoid_refines : ∀ s₁ s₂ : State,
      (pcSetoidWith isa closure).r s₁ s₂ → TemplateEquiv Ψ isa.satisfies s₁ s₂)
    (h_lift_eq : ∀ (σ : SymSub Reg) (φ : SymPC Reg),
      isa.pc_lift σ φ = substSymPC σ φ)
    : SemClosed isa model closure := by
  intro b hb φ hφ s₁ s₂ h_equiv
  -- φ is a template instance
  obtain ⟨T, hT, v, hφ_eq⟩ := h_closure_inst φ hφ
  -- pc_lift b.sub φ = substSymPC b.sub (instantiatePC v T)
  rw [h_lift_eq, hφ_eq]
  -- Apply the core theorem
  exact templateClosed_preserves_lifted isa.satisfies model Ψ h_tclosed
    b hb T hT v s₁ s₂ (h_pcSetoid_refines s₁ s₂ h_equiv)

end VexISA
