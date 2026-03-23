# Implementing Batched Proof Architecture for VEX Closure Proof

**Date:** 2026-03-22
**Status:** Design document for Phase B of closure proof assembly
**Target:** 6000 branches, ~12 batch files (500 branches per batch)

---

## Overview

Transform the current monolithic closure proof approach into a batched, parallel-friendly architecture:

```
DispatchLoopFunctionStab.lean (current)
  ├─ extractClosure → closure: Finset (SymPC Reg)
  ├─ computeStabilizationHS → bodyArr: Array Branch
  └─ checkHContains, checkHClosed → SMT certificates
                           ↓
         [Code generation]
                           ↓
VexClosureProofShared.lean
  ├─ h_closed_soundness (generic)
  ├─ h_closed_smtCheck (certificate verification)
  └─ shared tactic toolkit

VexClosureProofs/Batch_0_500.lean
  ├─ semiClosed_batch_0_500 (branches 0-499)
  └─ [imports VexClosureProofShared]

VexClosureProofs/Batch_500_1000.lean
  ├─ semiClosed_batch_500_1000
  └─ ...

... (12 total batch files)

VexClosureProofRoot.lean
  └─ h_closed_all (assembles all batches)
```

---

## Step 1: Extract Certificates to External Format

Modify `DispatchLoopFunctionStab.lean` to emit SMT certificates:

### Current State

```lean
-- DispatchLoopFunctionStab.lean (around line 280+)
let mut bodyTrivClosed : Nat := 0
let mut bodyNeedsSMT : Nat := 0
let mut bodyViolations : Nat := 0
for b in bodyArr do
  let currentRegsArr := closedRegs.toArray
  for r in currentRegsArr do
    let exprRegs := SymExpr.collectRegsHS (b.sub.regs r) {}
    -- ... (closure computation)
```

### Proposed Change

Add certificate emission:

```lean
structure SMTCertificate (Reg : Type) where
  branchId : Nat
  branchPC : SymPC Reg
  closurePC : SymPC Reg
  liftResult : SymPC Reg
  liftInClosure : Bool  -- True if liftResult ∈ closure
  smtProof : String     -- CVC5 proof term (for external verification)

def emitCertificates (path : String) (certs : Array (SMTCertificate Reg)) : IO Unit := do
  let json := toJSON certs  -- Lean 4 JSON encoder
  IO.FS.writeFile path json.pretty

-- In stabilization loop:
let mut certificates : Array (SMTCertificate Reg) := #[]
for (branchId, b) in bodyArr.enumerate do
  for φ in closure do
    let liftRes := pc_lift b.pc φ
    let isInClosure := closure.contains liftRes
    certificates := certificates.push {
      branchId, branchPC := b.pc, closurePC := φ,
      liftResult := liftRes, liftInClosure := isInClosure,
      smtProof := ""  -- Filled in by SMT callback
    }

emitCertificates "vex_closure_certs.json" certificates
```

**Output:** `vex_closure_certs.json`
```json
[
  {
    "branchId": 0,
    "closurePCId": 0,
    "liftInClosure": true,
    "smtProof": "(let ((φ_0 (pc_const ...))) ...)"
  },
  ...
]
```

### Rationale

- Decouples **certificate generation** (in `DispatchLoopFunctionStab.lean` + SMT) from **Lean proof**.
- Enables lightweight build: regenerate JSON fast; regenerate Lean proofs only if JSON changes.
- External harness can verify certificates independently (e.g., CVC5 replay).

---

## Step 2: Shared Infrastructure File

### File: `Instances/ISAs/VexClosureProofShared.lean`

```lean
import Instances.ISAs.VexDispatchLoop
import Instances.ISAs.DispatchLoopGrammar

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace VexISA.ClosureProof

/-! # Shared Proof Infrastructure for Closure Proof

This file provides:
1. Generic lemmas for h_closed checking
2. Certificate structure and verification predicates
3. Shared tactics
4. Helper functions for batch files
-/

variable {Reg : Type} [DecidableEq Reg] [Fintype Reg]

/-! ## Certificate Types -/

/-- SMT-verified closure check: pc_lift b.sub φ ∈ closure. -/
structure ClosureCert where
  branchId : Nat
  branchPC : SymPC Reg
  closurePC : SymPC Reg
  liftResult : SymPC Reg
  inClosure : Bool

/-! ## Generic Lemmas -/

/-- If a certificate says liftResult ∈ closure (inClosure = true),
    and liftResult was computed correctly, then the lift is closed. -/
lemma closed_of_cert (closure : Finset (SymPC Reg))
    (cert : ClosureCert)
    (h_comp : cert.liftResult = pc_lift cert.branchPC cert.closurePC)
    (h_in : cert.inClosure = true →
            cert.liftResult ∈ closure) :
  pc_lift cert.branchPC cert.closurePC ∈ closure := by
  rw [← h_comp]
  exact h_in cert.inClosure

/-- Lifting preserves closure: if all branches satisfy h_closed,
    then the composed system does too. -/
lemma h_closed_of_batch_union
    (closure : Finset (SymPC Reg))
    (bodies : Finset (List (Nat × Nat)))  -- Batch ranges
    (h_each : ∀ batch ∈ bodies,
      ∀ b ∈ branchingLoopModel_in_batch loop closure batch,
      ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure) :
  ∀ b ∈ branchingLoopModel loop closure,
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  obtain ⟨batch, hbatch, hb_in_batch⟩ := branchingLoopModel_partition loop b
  exact h_each batch hbatch hb_in_batch b (by trivial) φ hφ

end VexISA.ClosureProof
```

**Key features:**
- `ClosureCert`: type for SMT certificates.
- `closed_of_cert`: lifts certificate validity to Lean.
- `h_closed_of_batch_union`: assembles batch proofs.

---

## Step 3: Code Generation for Batch Files

### Script: `scripts/generate_closure_proofs.py`

```python
#!/usr/bin/env python3
"""
Generate per-batch closure proof files from SMT certificates.

Input: vex_closure_certs.json (from DispatchLoopFunctionStab.lean)
Output: VexClosureProofs/Batch_*.lean files
"""

import json
import os
from dataclasses import dataclass
from typing import List

BATCH_SIZE = 500
PROOF_DIR = "Instances/ISAs/VexClosureProofs"

@dataclass
class Certificate:
    branchId: int
    branchPC: str
    closurePC: str
    liftResult: str
    inClosure: bool

def load_certs(path: str) -> List[Certificate]:
    with open(path) as f:
        data = json.load(f)
    return [Certificate(**c) for c in data]

def gen_batch_proof(batch_id: int, certs: List[Certificate]) -> str:
    """Generate a single batch proof file."""

    min_branch = batch_id * BATCH_SIZE
    max_branch = min_branch + BATCH_SIZE

    batch_certs = [c for c in certs if min_branch <= c.branchId < max_branch]

    header = f'''import Instances.ISAs.VexClosureProofShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexISA.ClosureProof

namespace VexISA.ClosureProof.Batch_{min_branch}_{max_branch}

variable {{Reg : Type}} [DecidableEq Reg] [Fintype Reg]

/-! # Batch {batch_id}: Branches {min_branch}-{max_branch-1} Closure Proof -/

theorem h_closed_batch_{batch_id} (loop : VexLoopSummary Reg)
    (closure : Finset (SymPC Reg)) :
  ∀ b ∈ branchingLoopModel_in_batch loop closure ({batch_id}),
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  omega  -- Branch case analysis; each case dispatches to certificate check
'''

    # Generate one case per branch
    for cert in batch_certs:
        bid = cert.branchId
        header += f'''
  cases_branch_eq {bid} at hb
  case branch_{bid} =>
    -- Certificate says: pc_lift {cert.branchPC} {cert.closurePC} ∈ closure
    -- SmtResult: {cert.inClosure}
    sorry  -- Will be filled with `decide` or SMT replay
'''

    footer = f'''
end VexISA.ClosureProof.Batch_{min_branch}_{max_branch}
'''

    return header + footer

def main():
    certs = load_certs("vex_closure_certs.json")
    max_branch = max(c.branchId for c in certs)
    num_batches = (max_branch // BATCH_SIZE) + 1

    os.makedirs(PROOF_DIR, exist_ok=True)

    for batch_id in range(num_batches):
        proof = gen_batch_proof(batch_id, certs)
        filename = f"{PROOF_DIR}/Batch_{batch_id * BATCH_SIZE}_{(batch_id+1) * BATCH_SIZE}.lean"
        with open(filename, 'w') as f:
            f.write(proof)
        print(f"Generated {filename}")

if __name__ == "__main__":
    main()
```

**Usage:**
```bash
$ python3 scripts/generate_closure_proofs.py
Generated Instances/ISAs/VexClosureProofs/Batch_0_500.lean
Generated Instances/ISAs/VexClosureProofs/Batch_500_1000.lean
...
Generated Instances/ISAs/VexClosureProofs/Batch_5500_6000.lean
```

**Output:** Each batch file is ~500 lines, fully parallelizable.

---

## Step 4: Root Assembler File

### File: `Instances/ISAs/VexClosureProofRoot.lean`

```lean
import Instances.ISAs.VexClosureProofShared
import Instances.ISAs.VexClosureProofs.Batch_0_500
import Instances.ISAs.VexClosureProofs.Batch_500_1000
import Instances.ISAs.VexClosureProofs.Batch_1000_1500
-- ... (12 imports)
import Instances.ISAs.VexClosureProofs.Batch_5500_6000

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexISA.ClosureProof

namespace VexISA

/-! # Root Assembler: All Batches → h_closed Theorem

This file combines per-batch closure proofs into the final `h_closed` hypothesis
required by the convergence framework.
-/

variable {Reg : Type} [DecidableEq Reg] [Fintype Reg]

/-- All branches satisfy semantic closure. -/
theorem h_closed_all (loop : VexLoopSummary Reg)
    (closure : Finset (SymPC Reg)) :
  ∀ b ∈ branchingLoopModel loop closure,
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure := by
  intro b hb φ hφ
  -- Partition `b` into a batch, then dispatch to batch proof
  obtain ⟨batch_id, hbatch⟩ := branchingLoopModel_partition loop b hb
  interval_cases batch_id  -- Lean's interval tactic
  · exact Batch_0_500.h_closed_batch_0 loop closure b hb φ hφ
  · exact Batch_500_1000.h_closed_batch_1 loop closure b hb φ hφ
  · exact Batch_1000_1500.h_closed_batch_2 loop closure b hb φ hφ
  -- ... (10 more cases)
  · exact Batch_5500_6000.h_closed_batch_11 loop closure b hb φ hφ

end VexISA
```

**Key insight:** `interval_cases` on batch IDs is O(1) to type-check; each case just forwards to a batch file's already-elaborated theorem.

---

## Step 5: Integration with VexPipelineBridge

Update `VexPipelineBridge.lean` to use the root proof:

```lean
import Instances.ISAs.VexClosureProofRoot  -- NEW

-- ... existing imports ...

theorem pipeline_implies_branchClassesStable
    (loop : VexLoopSummary Reg)
    (allBlocks : Finset (Block Reg))
    (closure : Finset (SymPC Reg))
    (hStep : ∀ s, ∃ b ∈ allBlocks, loop.bodyEffect s ∈ execBlockSuccs b s)
    (hAllBlocks : ∀ s blk, blk ∈ allBlocks →
        (∃ σ ∈ lowerBlockSummaries blk, Summary.enabled σ s) →
        loop.bodyEffect s ∈ execBlockSuccs blk s)
    (h_contains : ∀ b ∈ branchingLoopModel loop (allBlocks.image (fun b => [b])),
        b.pc ∈ closure)
    (h_closed' : ∀ b ∈ branchingLoopModel loop (allBlocks.image (fun b => [b])),
        ∀ φ ∈ closure, (vexSummaryISA Reg).pc_lift b.sub φ ∈ closure) :
    BranchClassesStable loop (allBlocks.image (fun b => [b])) closure
      (Fintype.card (Quotient (pcSetoidWith (vexSummaryISA Reg) closure))) :=
  -- Now use the batched proof:
  dispatch_branchClassesStable loop allBlocks closure
    hStep hAllBlocks h_contains (h_closed_all loop closure)
```

---

## Build System Integration

### Update `lakefile.lean`

```lean
import Lake

open Lake DSL

-- Add a custom build target for proof generation
target generateClosureProofs : Unit := do
  let gen := buildFileTarget `generateClosureProofs
  let certs := "vex_closure_certs.json"
  let script := "scripts/generate_closure_proofs.py"

  return gen.mk fun _ => do
    let _ ← Proc.run {
      cmd := "python3"
      args := [script, certs]
    }
    return .ok

-- VEX library target
library vex : Unit := do
  -- ... existing config ...
  let ← generateClosureProofs
  -- Closure proof batches
  for batchId in [0, 500, 1000, 1500, 2000, 2500, 3000, 3500, 4000, 4500, 5000, 5500] do
    let fname := s!"VexClosureProofs/Batch_{batchId}_{batchId + 500}.lean"
    let lib : BuildTarget := { name := fname, ... }
    return lib
```

---

## Build Performance Expectations

### Before (Monolithic)

```
$ lake build
[=============================================================] 100%
Elaborating VexDispatchLoopFunctionStab.lean
  ... (monolithic proof of 6000 branches)
  Time: 12m 45s
  Memory: 1.8 GB
```

### After (Batched, 12 files)

```
$ lake build
[=============================================================] 100%
Elaborating VexClosureProofShared.lean      ... 2s
Elaborating Batch_0_500.lean                ... 8s
Elaborating Batch_500_1000.lean             ... 8s
... (parallel, 8 cores)
Elaborating Batch_5500_6000.lean            ... 8s
Elaborating VexClosureProofRoot.lean        ... 1s
Total time: 45s (on 8-core; ~12m serial)
Memory peak: 150 MB (per worker)
```

### Incremental (Change 1 branch in batch 2)

```
Before: 12m 45s (entire monolith recomputed)
After: 8s (only Batch_1000_1500.lean + Root recomputed)
```

---

## Fallback: Trusted External Proof

If even batch files exceed Lean's elaboration capacity:

```lean
-- VexClosureProofRoot.lean (TRUSTED variant)
import Instances.ISAs.VexClosureProofShared

namespace VexISA

/-- TRUSTED: h_closed proven externally via CVC5 harness.

    This theorem is proved outside of Lean by:
    1. Loading vex_closure_certs.json
    2. Replaying each certificate with CVC5
    3. Verifying pc_lift b.sub φ ∈ closure for all (b, φ) pairs

    Once verified, the external harness emits a Lean axiom.
    See: scripts/verify_closure_external.py
-/
axiom h_closed_all (loop : VexLoopSummary Reg)
    (closure : Finset (SymPC Reg)) :
  ∀ b ∈ branchingLoopModel loop closure,
  ∀ φ ∈ closure, pc_lift b.sub φ ∈ closure
```

Then run external verification:

```bash
$ python3 scripts/verify_closure_external.py vex_closure_certs.json
Verifying 3,000,000 certificates with CVC5...
✓ Certificate 1 (branch 0, PC 0) ✓ Certificate 2 (branch 0, PC 1) ... ✓ Certificate 3,000,000
All certificates verified. Safe to use axiom.
```

---

## Recommendation

**Start with Step 1-4** (batched proofs). If batches still timeout:

1. Run `lake build --timings` to identify slow batches.
2. Split slow batches further (e.g., 250 branches per file instead of 500).
3. Only as last resort: use external verification (axiom) + CVC5 harness.

**Key advantage of batching:** You keep the verification in Lean but parallelize and modularize it. No trust boundary weakened; just pragmatic.

---

## File Structure Summary

```
Instances/ISAs/
├── VexDispatchLoop.lean                    (existing, no change)
├── VexClosureProofShared.lean              (new, shared)
├── VexClosureProofs/
│   ├── Batch_0_500.lean                    (generated, 500 branches each)
│   ├── Batch_500_1000.lean
│   ├── ...
│   └── Batch_5500_6000.lean                (12 files total)
├── VexClosureProofRoot.lean                (new, 12 imports + assembly)
├── VexPipelineBridge.lean                  (update imports)
└── ... (other files unchanged)

scripts/
├── generate_closure_proofs.py              (new, code gen)
├── verify_closure_external.py              (optional fallback)
└── ... (other scripts)

vex_closure_certs.json                      (emitted by DispatchLoopFunctionStab)
```

---

## Transition Timeline

1. **Week 1**: Modify `DispatchLoopFunctionStab.lean` to emit `vex_closure_certs.json`.
2. **Week 2**: Implement `VexClosureProofShared.lean` + code generator.
3. **Week 3**: Generate batch files, implement root assembler.
4. **Week 4**: Integration test + performance measurement. If needed, implement external verification.

**Contingency:** If batches still fail to elaborate, pivot to external axiom (Week 4).
