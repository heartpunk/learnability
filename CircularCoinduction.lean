import EffectiveObservability
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Circular Coinduction for Unbounded Loops

Extends the branch framework to handle unbounded loops. A loop body can now
be a full `CompTree` (with internal branching), not just a single `Branch`.

## Key Idea

A `LoopSummary` has:
- `body : CompTree Sub PC` — one iteration (may branch internally)
- `continues`/`exits : PC` — loop control conditions
- `bodyEffect : State → State` — deterministic concrete effect
- `bodyEffect_spec` — proof that bodyEffect agrees with treeBehavior

## Convergence

The loop branch set (`loopBranchSet`) accumulates symbolic branches by
composing the body's denotation with previously discovered branches.
It is monotone and, when it stabilizes, gives a complete branch model.

**Worst case:** (1 + B)^K branches (exponential in unrolling depth K).
**With absorptivity:** B * K branches (linear). Absorptivity holds when
  branches in the same PC-equivalence class compose identically — true for
  parsers and other programs with finite symbolic state. This follows from
  the `pcSetoid` congruence in Quotient.lean.

## Connection to Stalagmite

Stubs in stalagmite ARE loop summaries. Co-refinement IS circular coinduction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## Loop Summary -/

section LoopSummary

variable {Sub PC State : Type*}

/-- A loop summary: characterizes a while loop by its body (a CompTree with
    possible internal branching), continue/exit conditions, and a deterministic
    effect function.

    The determinism field reflects that compiled programs are deterministic:
    given a concrete state, exactly one path through the body fires. The
    `bodyEffect_spec` biconditional formalizes this: `treeBehavior` relates
    `s` to `s'` iff `s' = bodyEffect s`. This rules out the body having
    multiple successors for any given state. -/
structure LoopSummary (Sub PC State : Type*) (isa : SymbolicISA Sub PC State) where
  /-- The computation tree for one loop iteration (may have internal choice). -/
  body : CompTree Sub PC
  /-- Condition for loop to repeat (checked after body executes). -/
  continues : PC
  /-- Condition for loop to exit (checked after body executes). -/
  exits : PC
  /-- Deterministic effect of one iteration on concrete states. -/
  bodyEffect : State → State
  /-- The effect function IS the tree's behavior: `treeBehavior isa body s s'`
      holds iff `s' = bodyEffect s`. Encodes determinism — exactly one
      successor per state. -/
  bodyEffect_spec : ∀ s s', CompTree.treeBehavior isa body s s' ↔ s' = bodyEffect s

variable (isa : SymbolicISA Sub PC State)

/-- Iterate the body effect n times. Computable, deterministic. -/
def iterateBody (summary : LoopSummary Sub PC State isa) (n : ℕ) (s : State) : State :=
  summary.bodyEffect^[n] s

/-- Zero iterations = identity. -/
theorem iterateBody_zero (summary : LoopSummary Sub PC State isa) (s : State) :
    iterateBody isa summary 0 s = s := rfl

/-- Iteration unfolds: n+1 steps = one step then n steps. -/
theorem iterateBody_succ (summary : LoopSummary Sub PC State isa) (n : ℕ) (s : State) :
    iterateBody isa summary (n + 1) s =
    iterateBody isa summary n (summary.bodyEffect s) := by
  simp [iterateBody, Function.iterate_succ, Function.comp]

end LoopSummary


/-! ## While Loop Behavior -/

section WhileLoop

variable {Sub PC State : Type*} (isa : SymbolicISA Sub PC State)

/-- The behavior of a while loop:
    `while continues { body }` relates s to s' when there exists
    some number of iterations n such that body executes n times,
    `continues` holds after each intermediate iteration (but not the last),
    and `exits` holds after the final iteration.

    For n = 0: just check exits at the initial state (zero iterations).
    For n ≥ 1: continues holds at iterations 1..n-1, exits at iteration n. -/
def whileBehavior (summary : LoopSummary Sub PC State isa) : State → State → Prop :=
  fun s s' => ∃ n,
    (iterateBody isa summary n s = s') ∧
    (∀ k, k + 1 < n → isa.satisfies (summary.bodyEffect^[k + 1] s) summary.continues) ∧
    isa.satisfies (summary.bodyEffect^[n] s) summary.exits

/-- A loop summary is **sound** when the body captures the one-step behavior
    and the continue/exit conditions are exhaustive. -/
def LoopSummary.Sound (summary : LoopSummary Sub PC State isa)
    (oneStepBehavior : State → State → Prop) : Prop :=
  (∀ s, oneStepBehavior s (summary.bodyEffect s)) ∧
  (∀ s, isa.satisfies s summary.continues ∨ isa.satisfies s summary.exits)

end WhileLoop


/-! ## Loop Branch Set

The symbolic branches accumulated after n unrollings of the loop body. -/

section LoopBranchSet

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Symbolic branches after n unrollings.
    - 0 unrollings: {skip}
    - n+1: previous ∪ compose(body_branches, previous) -/
def loopBranchSet (summary : LoopSummary Sub PC State isa) :
    ℕ → Finset (Branch Sub PC)
  | 0 => {Branch.skip isa}
  | n + 1 => loopBranchSet summary n ∪
      composeBranchFinsets isa (CompTree.denot isa summary.body) (loopBranchSet summary n)

/-- The loop branch set is monotone. -/
theorem loopBranchSet_mono (summary : LoopSummary Sub PC State isa) :
    ∀ n, loopBranchSet isa summary n ⊆ loopBranchSet isa summary (n + 1) := by
  intro n
  show loopBranchSet isa summary n ⊆
    loopBranchSet isa summary n ∪
      composeBranchFinsets isa (CompTree.denot isa summary.body) (loopBranchSet isa summary n)
  exact Finset.subset_union_left

/-- Monotonicity extended to any gap. -/
theorem loopBranchSet_mono' (summary : LoopSummary Sub PC State isa) :
    ∀ n m, n ≤ m → loopBranchSet isa summary n ⊆ loopBranchSet isa summary m := by
  intro n m h
  induction h with
  | refl => exact Finset.Subset.refl _
  | step h ih => exact Finset.Subset.trans ih (loopBranchSet_mono isa summary _)

/-- After stabilization, no further unrollings add branches. -/
theorem loopBranchSet_stable (summary : LoopSummary Sub PC State isa) (K : ℕ)
    (h_stab : loopBranchSet isa summary K = loopBranchSet isa summary (K + 1)) :
    ∀ n, n ≥ K → loopBranchSet isa summary n = loopBranchSet isa summary K := by
  intro n hn
  induction n with
  | zero =>
      have hK : K = 0 := by omega
      rw [hK]
  | succ m ih =>
    by_cases hm : m ≥ K
    · -- m ≥ K, so by IH: S(m) = S(K)
      have hm_eq := ih hm
      -- S(m+1) = S(m) ∪ compose(body, S(m)) = S(K) ∪ compose(body, S(K)) = S(K+1) = S(K)
      show loopBranchSet isa summary m ∪
          composeBranchFinsets isa (CompTree.denot isa summary.body)
            (loopBranchSet isa summary m) =
        loopBranchSet isa summary K
      rw [hm_eq]
      -- Goal: S(K) ∪ compose(body, S(K)) = S(K)
      -- h_stab : S(K) = S(K+1) = S(K) ∪ compose(body, S(K))
      exact h_stab.symm
    · -- m < K, so m + 1 ≤ K, and since m + 1 ≥ K (from hn), m + 1 = K
      have : m + 1 = K := by omega
      rw [this]

/-- **Convergence theorem.**

    If the branch set stabilizes at step K, it equals the branch set at K
    for all subsequent steps. The stabilized set is the complete branch
    model for the loop (up to the equivalence classes that cause stabilization).

    The cardinality of the stabilized set depends on the program:
    - Worst case: (1 + B)^K (exponential, no branch collapsing)
    - With absorptivity: ≤ 1 + B * K (linear, see `absorptive_card_bound`) -/
theorem symbolic_loop_convergence
    (summary : LoopSummary Sub PC State isa) (K : ℕ)
    (h_stab : loopBranchSet isa summary K = loopBranchSet isa summary (K + 1)) :
    ∀ n, n ≥ K → loopBranchSet isa summary n = loopBranchSet isa summary K :=
  loopBranchSet_stable isa summary K h_stab


/-! ### Absorptive Composition Bound

When composition is "absorptive" — each unrolling adds at most B new
branches regardless of how large the existing set is — the total branch
count is linear: at most 1 + B * K.

This holds for programs where branches in the same PC-equivalence class
compose identically (the congruence property from Quotient.lean). In
particular, it holds for parsers and other finite-state programs. -/

/-- Absorptivity: composing body branches with the existing set adds at most
    B new branches per step. -/
def Absorptive (summary : LoopSummary Sub PC State isa) : Prop :=
  ∀ n, (composeBranchFinsets isa (CompTree.denot isa summary.body)
          (loopBranchSet isa summary n) \
        loopBranchSet isa summary n).card ≤
    (CompTree.denot isa summary.body).card

/-- Under absorptivity, each step increases the branch set by at most B. -/
theorem absorptive_step_bound (summary : LoopSummary Sub PC State isa)
    (h_abs : Absorptive isa summary) (n : ℕ) :
    (loopBranchSet isa summary (n + 1)).card ≤
    (loopBranchSet isa summary n).card + (CompTree.denot isa summary.body).card := by
  -- S(n+1) = S(n) ∪ compose(body, S(n))
  -- |A ∪ B| = |A| + |B \ A| (disjoint decomposition)
  show (loopBranchSet isa summary n ∪
      composeBranchFinsets isa (CompTree.denot isa summary.body)
        (loopBranchSet isa summary n)).card ≤
    (loopBranchSet isa summary n).card + (CompTree.denot isa summary.body).card
  let A := loopBranchSet isa summary n
  let B := composeBranchFinsets isa (CompTree.denot isa summary.body)
              (loopBranchSet isa summary n)
  -- |A ∪ B| ≤ |A| + |B| (standard), but we need the tighter |A| + |B \ A|.
  -- Key: |A ∪ B| + |A ∩ B| = |A| + |B|, so |A ∪ B| = |A| + |B| - |A ∩ B|
  -- Also |B \ A| = |B| - |A ∩ B|, so |A ∪ B| = |A| + |B \ A|.
  -- We have |B \ A| ≤ denot.card by absorptivity.
  have h_card_eq : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have h_sdiff_card : (B \ A).card + (A ∩ B).card = B.card := by
    rw [Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter B A
  -- So (A ∪ B).card = A.card + B.card - (A ∩ B).card = A.card + (B \ A).card
  have h_union : (A ∪ B).card = A.card + (B \ A).card := by omega
  rw [h_union]
  have h_sdiff_le := h_abs n
  -- (B \ A) is definitionally equal to the sdiff in h_abs
  change A.card + (B \ A).card ≤ A.card + (CompTree.denot isa summary.body).card
  exact Nat.add_le_add_left h_sdiff_le A.card

/-- **Linear bound under absorptivity: total branches ≤ 1 + B * K.** -/
theorem absorptive_card_bound (summary : LoopSummary Sub PC State isa)
    (h_abs : Absorptive isa summary) (n : ℕ) :
    (loopBranchSet isa summary n).card ≤
      1 + (CompTree.denot isa summary.body).card * n := by
  induction n with
  | zero => simp [loopBranchSet, Finset.card_singleton]
  | succ k ih =>
    have h_step := absorptive_step_bound isa summary h_abs k
    have h_mul : (CompTree.denot isa summary.body).card * (k + 1) =
        (CompTree.denot isa summary.body).card * k +
        (CompTree.denot isa summary.body).card :=
      Nat.mul_succ _ k
    omega

end LoopBranchSet


/-! ## Finite State Convergence (Corollary)

When the concrete state space is finite, stabilization is guaranteed by
pigeonhole. Provides one way to discharge the stabilization hypothesis,
but the practical bound comes from domain knowledge (e.g., parser states),
not state exhaustion. -/

section FiniteConvergence

variable {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
  (isa : SymbolicISA Sub PC State)

/-- Iterating a periodic function: if `f^[p] x = x` with `p > 0`,
    then `f^[n] x = f^[n % p] x`. -/
private theorem iterate_mod_of_periodic {α : Type*} {f : α → α} {x : α} {p : ℕ}
    (_hp : 0 < p) (h : f^[p] x = x) (n : ℕ) :
    f^[n] x = f^[n % p] x := by
  have key : ∀ m, f^[p * m] x = x := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Nat.mul_succ, Function.iterate_add, Function.comp_apply, h, ih]
  conv_lhs => rw [show n = n % p + p * (n / p) from (Nat.mod_add_div n p).symm]
  rw [Function.iterate_add, Function.comp_apply, key]

/-- If the state space is finite, the body effect's orbit must cycle.
    This gives a concrete (though potentially large) stabilization bound. -/
theorem finite_effect_convergence
    [Fintype State] [DecidableEq State]
    (f : State → State) :
    ∃ maxIter,
      ∀ n, n ≥ maxIter →
        ∀ s : State, f^[n] s ∈
          Finset.image (fun k => f^[k] s) (Finset.range maxIter) := by
  use Fintype.card State + 1
  intro n hn s
  have h_card : Fintype.card State < Fintype.card (Fin (Fintype.card State + 1)) := by
    simp [Fintype.card_fin]
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun (k : Fin (Fintype.card State + 1)) => f^[k.val] s) h_card
  have i_ne_j : i ≠ j := by intro h; exact hij (Fin.ext h)
  obtain ⟨a, b, hab, h_eq, hb⟩ : ∃ a b, a < b ∧ f^[a] s = f^[b] s ∧ b < Fintype.card State + 1 := by
    rcases Nat.lt_or_gt_of_ne i_ne_j with h | h
    · exact ⟨i, j, h, heq, hj⟩
    · exact ⟨j, i, h, heq.symm, hi⟩
  have p_pos : 0 < b - a := Nat.sub_pos_of_lt hab
  have h_periodic : f^[b - a] (f^[a] s) = f^[a] s := by
    have : f^[b] s = f^[b - a] (f^[a] s) := by
      conv_lhs => rw [show b = (b - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    rw [← this, ← h_eq]
  have h_reduce : ∀ m, m ≥ a → f^[m] s = f^[a + (m - a) % (b - a)] s := by
    intro m hm
    have h1 : f^[m] s = f^[m - a] (f^[a] s) := by
      conv_lhs => rw [show m = (m - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    have h2 : f^[m - a] (f^[a] s) = f^[(m - a) % (b - a)] (f^[a] s) :=
      iterate_mod_of_periodic p_pos h_periodic _
    have h3 : f^[(m - a) % (b - a)] (f^[a] s) = f^[a + (m - a) % (b - a)] s := by
      conv_rhs => rw [show a + (m - a) % (b - a) = (m - a) % (b - a) + a from by omega]
      rw [Function.iterate_add, Function.comp_apply]
    rw [h1, h2, h3]
  have h_bound : ∀ m, m ≥ a → a + (m - a) % (b - a) < Fintype.card State + 1 := by
    intro m _
    have : (m - a) % (b - a) < b - a := Nat.mod_lt _ p_pos
    omega
  have hn' : n ≥ a := by omega
  rw [h_reduce n hn']
  apply Finset.mem_image.mpr
  exact ⟨a + (n - a) % (b - a), Finset.mem_range.mpr (h_bound n hn'), rfl⟩

end FiniteConvergence
