import Core.LTS
import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# Bridge: Our LTS → Cslib LTS

Since `LTS` extends `Cslib.LTS`, cslib's bisimulation and simulation
theorems apply directly via `.toLTS`. This file provides explicit
bridge lemmas connecting our definitions to cslib's vocabulary.

## Main results

- `LTS.toCslibBisimulation`: symmetric simulation on a single LTS
  implies cslib `IsBisimulation`.
- `LTS.toCslibBisimilarity`: states related by such a relation are
  cslib-bisimilar (`~[lts.toLTS]`).
- `LTS.simulates_toCslibBisimulation`: two `Simulates` in opposite
  directions (our vocabulary) yield cslib `IsBisimulation`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LTS

variable {S L : Type*}

/-! ## Direct bridge: raw conditions → cslib IsBisimulation -/

/-- A relation satisfying both forward and backward matching on a single
    LTS is a cslib `IsBisimulation`. -/
theorem toCslibBisimulation (lts : LTS S L)
    (R : S → S → Prop)
    (h_fwd : ∀ s₁ s₂ μ s₁', R s₁ s₂ → lts.Tr s₁ μ s₁' →
      ∃ s₂', lts.Tr s₂ μ s₂' ∧ R s₁' s₂')
    (h_bwd : ∀ s₁ s₂ μ s₂', R s₁ s₂ → lts.Tr s₂ μ s₂' →
      ∃ s₁', lts.Tr s₁ μ s₁' ∧ R s₁' s₂') :
    lts.toLTS.IsBisimulation R := by
  intro s₁ s₂ hr μ
  exact ⟨fun s₁' h => h_fwd s₁ s₂ μ s₁' hr h,
         fun s₂' h => h_bwd s₁ s₂ μ s₂' hr h⟩

/-- States related by a symmetric simulation are cslib-bisimilar. -/
theorem toCslibBisimilarity (lts : LTS S L)
    (R : S → S → Prop) (s₁ s₂ : S)
    (h_fwd : ∀ a b μ a', R a b → lts.Tr a μ a' →
      ∃ b', lts.Tr b μ b' ∧ R a' b')
    (h_bwd : ∀ a b μ b', R a b → lts.Tr b μ b' →
      ∃ a', lts.Tr a μ a' ∧ R a' b')
    (hr : R s₁ s₂) :
    Cslib.Bisimilarity lts.toLTS s₁ s₂ :=
  ⟨R, hr, toCslibBisimulation lts R h_fwd h_bwd⟩

/-! ## Bridge from our `Simulates` structure

Our `Simulates simulating simulated R` captures one direction:
when `simulated` steps, `simulating` can match. Two `Simulates` in
opposite directions (with appropriately related witness relations)
give both directions of cslib `IsBisimulation`. -/

/-- Two opposite-direction simulations on the same LTS yield cslib
    `IsBisimulation`. The witness relation from the forward simulation
    is used; the backward simulation must use the flipped relation. -/
theorem simulates_toCslibBisimulation (lts : LTS S L)
    (R : S → S → Prop)
    (h_sim_fwd : ∀ (s₁ s₂ : S) (μ : L) (s₂' : S),
      R s₁ s₂ → lts.Tr s₂ μ s₂' → ∃ s₁', lts.Tr s₁ μ s₁' ∧ R s₁' s₂')
    (h_sim_bwd : ∀ (s₁ s₂ : S) (μ : L) (s₁' : S),
      R s₁ s₂ → lts.Tr s₁ μ s₁' → ∃ s₂', lts.Tr s₂ μ s₂' ∧ R s₁' s₂') :
    lts.toLTS.IsBisimulation R :=
  toCslibBisimulation lts R h_sim_bwd h_sim_fwd

end LTS
