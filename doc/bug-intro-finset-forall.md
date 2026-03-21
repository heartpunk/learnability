# Bug: `intro` fails on `→` when LHS is `∀ x ∈ Finset, ...`

## Symptom

After introducing 6 binders, the goal displays as:
```
⊢ myEquiv basis satisfies s₁ s₂ → satisfies s₁ (lift b.sub φ) ↔ satisfies s₂ (lift b.sub φ)
```
But `intro h` fails with "no additional binders or let bindings in the goal to introduce."

## Root Cause (hypothesis)

`myEquiv` unfolds to `∀ φ ∈ basis, satisfies s₁ φ ↔ satisfies s₂ φ`. When Lean sees
`(∀ φ ∈ basis, satisfies s₁ φ ↔ satisfies s₂ φ) → (satisfies s₁ X ↔ satisfies s₂ X)`,
it parses the `→` as binding INSIDE the `∀ φ ∈ basis` quantifier, making the whole thing
`∀ φ ∈ basis, (satisfies s₁ φ ↔ satisfies s₂ φ) → (satisfies s₁ X ↔ satisfies s₂ X)`.

This is because `→` has lower precedence than `↔`, and `∀ φ ∈ basis, P → Q` parses as
`∀ φ ∈ basis, (P → Q)`, not `(∀ φ ∈ basis, P) → Q`.

So `intro` sees MORE `∀` binders (one per basis element), not an arrow.
The displayed goal is misleading — it shows `myEquiv` folded but Lean internally has it unfolded.

## Minimal Reproduction

```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

variable {State PC Sub : Type} [DecidableEq Sub] [DecidableEq PC]

structure Branch (Sub PC : Type) where
  sub : Sub
  pc : PC

def myEquiv (basis : Finset PC) (satisfies : State → PC → Prop) (s₁ s₂ : State) : Prop :=
  ∀ φ ∈ basis, satisfies s₁ φ ↔ satisfies s₂ φ

example (model : Finset (Branch Sub PC)) (basis : Finset PC)
    (satisfies : State → PC → Prop)
    (lift : Sub → PC → PC)
    (h_state_eq : ∀ s₁ s₂ : State, myEquiv basis satisfies s₁ s₂ → s₁ = s₂) :
    ∀ b ∈ model, ∀ φ ∈ basis, ∀ s₁ s₂ : State,
      myEquiv basis satisfies s₁ s₂ →
      satisfies s₁ (lift b.sub φ) ↔ satisfies s₂ (lift b.sub φ) := by
  intro b _ φ _ s₁ s₂
  intro h_equiv  -- FAILS: "no additional binders"
  sorry
```

## Likely Fix

Make `pcEquiv`/`myEquiv` `@[irreducible]` so Lean doesn't unfold it during `intro`,
or wrap the hypothesis type with parentheses in the theorem statement:
`(myEquiv basis satisfies s₁ s₂) → ...` might not help since Lean still unfolds.

Alternative: use `SemClosed` directly instead of spelling out the `∀ b ∈ model, ∀ φ ∈ basis, ...`
return type, since `SemClosed` is an opaque def that won't unfold the same way.

## Affected Theorems

- `VexPipelineBridge.lean`: `h_value_determined_of_state_agreement`
- `TemplateConvergence.lean`: `semClosed_of_valueDetermined`
