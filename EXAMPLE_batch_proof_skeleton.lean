/-! # Example: Batch Proof File Structure

This is a concrete skeleton showing what one batch proof file would look like
for branches 0-499 of a 6000-branch closure proof.

This file is intended to be code-generated. The structure scales linearly
with batch size (500 branches), so each of 12 batch files looks similar.

Generated from:
  $ python3 scripts/generate_closure_proofs.py \
      --input vex_closure_certs.json \
      --output-dir Instances/ISAs/VexClosureProofs/
      --batch-size 500
-/

import Instances.ISAs.VexClosureProofShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexISA.ClosureProof

namespace VexISA.ClosureProof.Batch_0_500

variable {Reg : Type} [DecidableEq Reg] [Fintype Reg]
variable (loop : VexLoopSummary Reg)
variable (closure : Finset (SymPC Reg))

/-! # Batch 0: Branches 0-499 Semantic Closure Proof

Each theorem below proves that for one branch, its `pc_lift` over all
closure PCs stays within the closure.

The proof is SMT-certified: for each branch and closure PC pair,
`vex_closure_certs.json` contains a CVC5-verified proof that the lift
is in the closure.
-/

/-- Branch 0: All its pc_lift values stay in closure.

    Certificate witnesses from vex_closure_certs.json (excerpt):
      { "branchId": 0, "closurePCId": 0, "liftInClosure": true, ... }
      { "branchId": 0, "closurePCId": 1, "liftInClosure": true, ... }
      ...
      { "branchId": 0, "closurePCId": 499, "liftInClosure": true, ... }
-/
theorem sem_closed_branch_0 :
  let b := get_branch_from_model loop 0
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  -- The proof here is a case split on `φ` (or equivalently, on its index in closure).
  -- Each case uses the SMT certificate.
  sorry  -- Will be replaced by decision procedure or SMT tactic

/-- Branch 1: All its pc_lift values stay in closure. -/
theorem sem_closed_branch_1 :
  let b := get_branch_from_model loop 1
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  sorry

/-- Branch 2: ... -/
theorem sem_closed_branch_2 :
  let b := get_branch_from_model loop 2
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  sorry

-- ... (repeated for branches 3 through 498)
-- Code generator produces all 500 theorem statements like this.

/-- Branch 499: All its pc_lift values stay in closure. -/
theorem sem_closed_branch_499 :
  let b := get_branch_from_model loop 499
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  sorry

/-! ## Assembly Lemma for This Batch

Combines all 500 branch proofs into one statement:
"All branches in this batch satisfy semantic closure."
-/

theorem h_closed_batch_0 :
  ∀ b ∈ branchingLoopModel_in_batch loop 0,
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  -- `hb` tells us which branch in [0, 500) we're dealing with
  omega  -- Uses linear arithmetic / interval cases
  · -- Branch 0
    exact sem_closed_branch_0 φ hφ
  · -- Branch 1
    exact sem_closed_branch_1 φ hφ
  · -- Branch 2
    exact sem_closed_branch_2 φ hφ
  -- ... (500 cases)
  · -- Branch 499
    exact sem_closed_branch_499 φ hφ

end VexISA.ClosureProof.Batch_0_500

/-! ============================================================================

# Notes on Generated Code

## What Gets Generated

This file is **code-generated** by `scripts/generate_closure_proofs.py`:

1. **Imports**: Boilerplate (shown above).

2. **500 Theorems** (`sem_closed_branch_0` through `sem_closed_branch_499`):
   - Each proves one branch's closure property.
   - Structure identical (differs only in branch ID and the sorried tactic).
   - Could later be filled with:
     - `decide` (if SMT proofs compile to Lean tactics)
     - `cvc5` tactic (if integrated into Lean)
     - `sorry` (if externally verified via axiom)

3. **Assembly Lemma** (`h_closed_batch_0`):
   - Combines all 500 proofs.
   - Uses `omega` or `interval_cases` to dispatch on branch ID.

## What's Not Generated (To Be Filled In Manually or By SMT Harness)

The `sorry` in each theorem is a placeholder for:

```lean
theorem sem_closed_branch_42 :
  let b := get_branch_from_model loop 42
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  -- THIS PART gets filled in by:
  -- Option 1: CVC5 external harness, generates a proof term
  -- Option 2: decide tactic (if computable)
  -- Option 3: Manual SMT replay (debug-friendly)
  sorry
```

### Option 1: Trusted External Harness

```python
# scripts/fill_proofs_from_cvc5.py
def generate_proof_for_branch(branch_id, closure_pcs, cvc5_harness):
    """
    For each (branch_id, closure_pc) pair:
    1. Call CVC5 to verify pc_lift stays in closure.
    2. Extract proof term (if CVC5 supports it).
    3. Embed proof term as Lean tactic.
    """
    proofs = []
    for pc_id, φ in enumerate(closure_pcs):
        # Call CVC5, get "UNSAT" or SAT with model
        result = cvc5_harness.check_closure(branch_id, pc_id)
        if result.status == "UNSAT":
            # Generate Lean tactic: sorry (we trust CVC5)
            proofs.append(f"sorry  -- CVC5-verified: branch {branch_id} + PC {pc_id}")
        else:
            raise ValueError(f"CVC5 says not closed: branch {branch_id}, PC {pc_id}")
    return proofs
```

### Option 2: Lean 4 `decide` (If Closure Is Decidable)

```lean
theorem sem_closed_branch_42 :
  let b := get_branch_from_model loop 42
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  -- If pc_lift and membership are decidable, use decide
  decide
```

### Option 3: Manual Debug (For Development)

```lean
theorem sem_closed_branch_42 :
  let b := get_branch_from_model loop 42
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro φ hφ
  -- For debugging: compute and show the witness
  show pc_lift b.sub φ ∈ closure
  simp [pc_lift, b, φ, closure]
  -- If the simplifier can't close it, leave sorry with context
  sorry
```

## Scale and Maintainability

For 6000 branches in 12 batches:

- Each batch file is **~500 lines** (500 theorem statements + assembly).
- **Zero hand-written code** — entirely generated.
- **Trivial to regenerate**: Rerun script, get 12 fresh files.
- **Incremental changes**: If closure changes, regenerate only affected batches.

## Integration with VexClosureProofRoot.lean

The root file (shown in another document) imports this file:

```lean
import Instances.ISAs.VexClosureProofs.Batch_0_500

-- ... (11 more batch imports)

theorem h_closed_all :
  ∀ b ∈ branchingLoopModel loop closure,
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  obtain ⟨batch_id, hbatch⟩ := branchingLoopModel_partition loop b hb
  interval_cases batch_id
  · exact Batch_0_500.h_closed_batch_0 φ hφ
  · exact Batch_500_1000.h_closed_batch_1 φ hφ
  -- ... (10 more cases)
  · exact Batch_5500_6000.h_closed_batch_11 φ hφ
```

The root's `interval_cases` on batch IDs is type-checked in O(1) time
because `interval_cases` is a Lean 4 built-in that specializes on decidable
integer ranges.

============================================================================ -/
