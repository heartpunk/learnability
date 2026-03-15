# Region-Based Store Elimination: Analysis & Remaining Violation Categories

## Context

The dispatch loop pipeline composes symbolic branches iteratively until the
branch set stabilizes. Each composition prepends stores (register writes) and
grows memory terms. Path conditions (PCs) reference loads from memory. For the
closure to be "closed," every lifted PC (branch substitution applied to a
closure guard) must syntactically match some closure member.

Without simplification, store chains grow unboundedly and closedness is
impossible. The simplifier resolves load-after-store patterns: when a load
address matches a store address, substitute the stored value. When they
provably differ, skip the store and recurse into the inner memory.

The "provably differ" part is where region-based elimination enters.

## What's Been Done (3 commits)

### Commit 1: `mwyxzlmt` — ELF regions + region-aware simplifier

Extracted memory regions from CLE (angr's ELF loader) into the JSON pipeline
input. Added `MemRegion`, `RegionTag` (loaded idx | stack), `classifyAddr`,
and region-aware simplifier variants (`simplifyLoadStoreExprR/MemR/PCR`).

Key design decision: separate R variant functions rather than adding a default
parameter to existing functions. Lean 4 default params don't backtrack —
adding `(classify : Option (AddrClassifier Reg) := none)` as a first param
breaks existing call sites. Keeping originals untouched preserves all
soundness proofs in `VexSimplificationSoundness.lean`.

`resolveLoadFrom` extended with optional classifier (last param, default
none). When store and load addresses classify to different `RegionTag`s,
the store is skipped.

### Commit 2: `tusuvnwl` — closure PC simplification

Closure PCs from `extractClosure` were raw/unsimplified while lifted PCs
went through the region-aware simplifier. Normal form mismatch prevented
syntactic matches even for trivially equal pairs.

Fix: `closure.map (simplifyLoadStorePCR clf)` right after `extractClosure`.

Result for next_sym: trivial 22→34/98, violations 76→64.

### Commit 3: `usotvkpr` — indirect base-memory load classification

Extended `classifyAddr` to handle `load(base_mem, const)` patterns. When the
constant address falls in a loaded ELF region (GOT, data, etc.), the loaded
pointer targets the loaded image and can't alias with stack addresses.

Factored the region lookup into `lookupRegion` helper (eliminates duplication
between `.const c` case and new `.load _ .base (.const c)` case).

Sound on x86-64: statically-initialized pointers (GOT entries, data section
pointers) don't point into the runtime stack.

Result for next_sym: violations 64→32 (halved).

## Remaining 32 Violations (next_sym, Phase 1)

All 32 involve guards φ[3] or φ[4] (and their interactions with branches
b[0]–b[4]). The closure has 7 PCs; 10 non-closed lifted PCs shown in
diagnostic output.

### Closure PCs (simplified notation)

```
φ[0]:  load_32(base_mem, load_64(base_mem, 0x500030)) == 14
φ[1]:  true
φ[2]:  ¬φ[0]
φ[3]:  load_32(store(base_mem, rbp-16, rax), and64(rax, mask)) == 0
φ[4]:  ¬φ[3]
φ[5]:  load_32(base_mem, load_64(base_mem, 0x500030)) == 12
φ[6]:  ¬φ[5]
```

Where `mask` = `0xFFFFFFFFFFFFFFFF` (AND with all-ones = identity, i.e. noise).

### Category C: `and64` identity mask (cross-cutting)

**Pattern:** `and64(x, 0xFFFFFFFFFFFFFFFF)` appears in load addresses and
intermediate values throughout. AND with all-ones is identity — pure syntactic
noise that inflates expressions and prevents matching.

**Fix:** Add `foldAnd64` to the simplifier, analogous to existing `foldAdd64`
and `foldSub64`. Folds:
- `and64(x, UInt64.max) → x`
- `and64(UInt64.max, x) → x`
- `and64(x, 0) → 0`
- `and64(c1, c2) → c1 &&& c2`

**Impact:** Reduces expression size in all 32 remaining pairs. Enables
Categories D and E to be more effective. Alone does not close any pairs.

### Category D: Dead store at same address (6 pairs)

**Pairs:** b[0]×φ[3,4], b[3]×φ[3,4], and similar patterns.

**Pattern:**
```
store(store(base_mem, rbp-16, rax), rbp-16, V)
```
Two stores at `rbp-16` — the inner store of `rax` is overwritten by the outer
store of `V`. The inner store is dead.

**Fix:** Dead store elimination in `simplifyLoadStoreMemR`: when
`store(store(mem, addr, v1), addr, v2)` and `addr` matches syntactically,
simplify to `store(mem, addr, v2)`.

**After fix + Category C:**
```
load_32(store(base_mem, rbp-16, V), V) == 0
```
Compare with φ[3] (after and64 folding):
```
load_32(store(base_mem, rbp-16, rax), rax) == 0
```

Same structure `f(X) == 0` but `X = rax` vs `X = V` where
`V = zext32(low32(load_32(store(base_mem, rbp-16, rax), rax)))`. These are
genuinely different PCs — checking the character at position V (next
iteration) vs position rax (current iteration). This is the **iteration
depth** problem: each loop iteration advances the input pointer.

**Impact:** Cleaner expressions. Does NOT close these pairs — they are
fundamentally non-closed because the closure would need to contain PCs for
every possible iteration depth. The pipeline converges via simplification
and signature dedup, not algebraic closedness.

### Category E: Null-page constant loads (2 pairs)

**Pairs:** b[2]×φ[3,4].

**Pattern:** Branch b[2] stores 0 at `rbp-16`. The load address (after and64
folding) becomes `and64(0, mask) = 0`. So:
```
load_32(store(store(store(base_mem, rbp-16, rax), rsp-8, 0x400A95), rbp-16, 0), 0) == 0
```

The load is from address 0 (the null page). Stores are at `rbp-16` (stack)
and `rsp-8` (stack). Address 0 is:
- NOT in any loaded ELF region (regions start at 0x400000+)
- NOT on the stack (stack is at 0x7fff...)
- The null page — unmapped on all modern OSes

If the classifier can prove `0 ≠ stack`, all stack stores skip and this
resolves to `load_32(base_mem, 0) == 0`, a deterministic value (practically
a NULL dereference — infeasible path).

**Fix:** Extend `classifyAddr` to classify constant addresses below a
threshold (e.g., the lowest region's vaddr) as a synthetic "low" region tag,
or simply: if the constant IS classified as `loaded idx`, the existing
machinery handles it; if it's NOT in any region but IS a constant, we know
it's not stack (stack addresses are register-relative). Add a fallback in
`resolveLoadFrom`: when load address is `.const` and store address classifies
as `stack`, skip the store.

**Impact:** 2 pairs resolve completely (infeasible path eliminated). Small
but meaningful — demonstrates constant-vs-stack non-aliasing.

### Category F: Computed struct-field store addresses (4 pairs)

**Pairs:** b[4]×φ[0,2,3,4].

**Pattern:** Store at `load_64(base_mem, rbp-16) + 16` — this is the callee's
struct pointer (loaded from a local variable at `rbp-16`) plus a field offset.
The store address is a heap/data structure field, not stack and not GOT.

```
store(base_mem, load_64(base_mem, rbp-16) + 16, rax)
```

Load addresses are either GOT constant (`0x500030`) or stack-relative
(`rbp-16`). The store address `*(rbp-16)+16` is:
- Computed from a stack load (`rbp-16` → stack value → struct pointer)
- Offset by a constant (+16 → struct field)
- Almost certainly a heap address, but we can't prove it

**Fix:** Would require classifying `add64(load_64(base_mem, stack_addr),
const)` — i.e., "pointer loaded from stack + offset." On x86-64, local
variables that hold pointers typically point to heap/data, not GOT or stack.
But this is an ABI assumption stronger than what we've used so far.

**Current assessment:** Deferred. These 4 pairs don't block the pipeline
(convergence works regardless). If needed later, options include:
1. ABI-aware classification (function arguments/locals → heap pointers)
2. Symbolic evaluation of base-memory loads at known-writable sections
3. Accepting these as inherent imprecision in a static analysis

## Violation Trajectory

```
          next_sym violations
Start:          76/98
Commit 1+2:     64/98   (region-aware simplifier + closure PC normalization)
Commit 3:       32/98   (indirect GOT load classification)
After C+D+E:    ~24/98  (projected: 6 from D still non-closed, 2 from E resolve)
Category F:     ~20/98  (4 pairs, requires ABI reasoning)
```

The remaining ~20-24 violations are fundamentally non-closed: they represent
the iteration depth problem where each loop iteration checks a different
character position. The pipeline converges despite this because branch
*behavior* (which registers change, which control flow paths exist) stabilizes
even as the specific character position varies.

## Architectural Note: Convergence vs. Closedness

The pipeline converges via **simplification + signature dedup**, not algebraic
closedness. After a few iterations:
- `simplifyLoadStorePC` resolves same-address store-then-load patterns
- `simplifyConst` collapses constant comparisons
- Signature dedup (PC structure hashing) identifies structurally identical
  branches across iterations

This means the closure is NOT algebraically closed, but the summary (branch
set) stabilizes anyway. For certification, the path forward is `SemClosed`
via `bv_decide` witnesses (per the certification plan), not syntactic
closedness. The simplification work here reduces expression sizes and helps
SMT find semantic equivalences, but the fundamental gap between syntactic
closedness and convergence remains.

## Files Modified

- `DispatchLoopEval.lean`: `lookupRegion`, `classifyAddr`, `resolveLoadFrom`,
  `simplifyLoadStoreExprR/MemR/PCR`, `simplifyBranchFull`, `parseMemRegions`,
  `loadFunctionsFromJSON`, `stratifiedFixpoint`, `computeFunctionStabilization`
- `DispatchLoopTestSubjects.lean`: `runTestSubject` destructures regions
- `extract_cfg.py`: `extract_memory_regions()` (Python, CLE integration)
- `parser_nt_blocks.json`: regenerated with `memory_regions` field
