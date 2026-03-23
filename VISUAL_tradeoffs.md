# Visual Tradeoff Analysis: Per-Branch Proof Architectures

---

## 1. Build Time Comparison

```
Monolithic (10-20 min)
├─ Phase 1: Parse & elaboration      │████████████████████│  8 min
├─ Phase 2: SMT queries (serial)      │████████████│         4 min
└─ Phase 3: Kernel type-check         │████│                 2 min
Total: ~14 min (sequential, 1 core)

Per-Branch (6000 files) (1-3 min)
├─ File generation                    │                      <1 sec
├─ Parallel elaboration (8 cores)     │████│                 1.5 min
├─ I/O overhead (6000 file imports)   │████████│             1.0 min
└─ Root assembly                      ││                     0.1 sec
Total: ~2.6 min (parallel, 8 cores, but I/O kills gains)

Batched (12 files) (20-45 sec) ← RECOMMENDED
├─ File generation                    │                      <1 sec
├─ Parallel elaboration (8 cores)     │████│                 0.5 min
├─ I/O overhead (12 file imports)     ││                     0.05 sec
└─ Root assembly                      ││                     0.1 sec
Total: ~45 sec (parallel, 8 cores, I/O minimal)

For comparison, monolithic run on all cores (N/A, serial):
└─ Kernel checking is not parallelizable
```

---

## 2. Proof Term Size Comparison

```
Monolithic: 10-50 MB
┌────────────────────────────────────────────────────────┐
│ Case tree node 0: Branch 0                              │
│   ├─ Subproof 0: pc_lift branch_0 φ_0 ∈ closure        │
│   ├─ Subproof 1: pc_lift branch_0 φ_1 ∈ closure        │
│   └─ ... (500 subproofs)                                │
│ Case tree node 1: Branch 1                              │
│   ├─ Subproof 0: pc_lift branch_1 φ_0 ∈ closure        │
│   └─ ...                                                 │
│ ...                                                      │
│ Case tree node 5999: Branch 5999                        │
│   └─ ... (500 subproofs)                                │
└────────────────────────────────────────────────────────┘
Total nodes: 6000 (branches) × 500 (closure PCs) = 3,000,000 proof nodes!

Per-Branch (6000 files): 3 MB total, 0.5 KB per file
┌─────────────────────┐ ┌─────────────────────┐ ┌─────────────────────┐
│ File 0: Branch 0    │ │ File 1: Branch 1    │ │ File 2: Branch 2    │ ...
│ ┌──────────────────┐│ │ ┌──────────────────┐│ │ ┌──────────────────┐│
│ │ 500 proof nodes  ││ │ │ 500 proof nodes  ││ │ │ 500 proof nodes  ││
│ └──────────────────┘│ │ └──────────────────┘│ │ └──────────────────┘│
└─────────────────────┘ └─────────────────────┘ └─────────────────────┘
Total: 6000 files × 500 nodes = 3,000,000 proof nodes (SAME as monolithic)
BUT: Each file elaborated independently, kernel checks ~500 nodes at a time

Batched (12 files): ~6 KB for proofs + 100 KB root = 106 KB
┌──────────────────────────────────────────────┐
│ File 0: Branches 0-499                        │
│ ┌────────────────────────────────────────────┤
│ │ 500 × 500 = 250,000 proof nodes             │
│ └────────────────────────────────────────────┘
├──────────────────────────────────────────────┤
│ File 1: Branches 500-999                      │
│ ┌────────────────────────────────────────────┤
│ │ 500 × 500 = 250,000 proof nodes             │
│ └────────────────────────────────────────────┘
│ ... (10 more batches)                         │
├──────────────────────────────────────────────┤
│ Root file:                                    │
│ ┌────────────────────────────────────────────┤
│ │ 12-case dispatch (~100 proof nodes)         │
│ └────────────────────────────────────────────┘
└──────────────────────────────────────────────┘
Total: same 3M nodes, but packaged in 12 chunks of 250K each
```

---

## 3. Memory Usage During Build

```
Monolithic: Peak 1-2 GB (entire 10-50 MB term in memory)
│
├─ Parse: 50 MB
├─ Elaborate: 500 MB
│  │ (Building proof term incrementally)
│  │ ┌──────────────────────────┐
│  │ │ Max: entire term in RAM  │ ← Bottleneck
│  │ └──────────────────────────┘
├─ Type-check: 1-2 GB
│  │ (Kernel traverses entire term)
│  │ ┌──────────────────────────────┐
│  │ │ Full term + environment      │ ← Memory peak
│  │ └──────────────────────────────┘
└─ Result: PASS/FAIL

Per-Branch (parallel, 8 cores): Peak 50 MB per core (400 MB total)
Core 1: ├─ File 0 (Branch 0-62)     : 10 MB peak
Core 2: ├─ File 1 (Branch 63-125)   : 10 MB peak
Core 3: ├─ File 2 (Branch 126-188)  : 10 MB peak
... (8 workers in parallel)
│
└─ Total peak: 8 × 50 MB = 400 MB (across all workers)
              vs. 1-2 GB (monolithic)
              → 4-5x memory savings!

Batched (parallel, 8 cores): Peak 100 MB per core (800 MB total)
Core 1: ├─ Batch 0  (Branches 0-499)   : 50 MB peak
Core 2: ├─ Batch 1  (Branches 500-999) : 50 MB peak
... (12 batches on 8 cores)
│
└─ Total peak: 8 × 100 MB = 800 MB (across all workers)
              vs. 1-2 GB (monolithic)
              → 2-3x memory savings
```

---

## 4. Incremental Build Time

```
Scenario: Change closure PC #42 (all branches must be re-verified)

Monolithic:
┌─ 1. Re-elaborate entire h_closed_all:        12 min
│     └─ Kernel must traverse all 6000 cases again
└─ Total: 12 min

Per-Branch (6000 files):
┌─ 1. Re-generate all 6000 batch files:        10 sec
├─ 2. Re-elaborate all 6000 batches:           150 sec (parallel)
│     └─ Each batch file elaborates in ~2 sec
├─ 3. I/O reload 6000 .olean files:            30 sec
└─ 4. Re-build root:                           1 sec
Total: ~200 sec (~3 min)

Batched (12 files):
┌─ 1. Re-generate batch files:                 2 sec (only affected batches)
├─ 2. Re-elaborate affected batches (12):      12 sec (parallel, 8 cores)
│     └─ 12 files × 1 sec each ÷ 8 cores = 1.5 sec
├─ 3. I/O reload batch .olean files:           0.1 sec
└─ 4. Re-build root:                           0.5 sec
Total: ~15 sec (with parallelism) ← HUGE win!
```

---

## 5. Kernel Checking Time (The Real Bottleneck)

```
Monolithic: O(6000 case nodes)
┌─ Kernel traverses all 6000 branches
│  ├─ Branch 0: ∈ closure? [check subsumption, unification, ...]  ~1 ms
│  ├─ Branch 1: ∈ closure? [...]                                  ~1 ms
│  ├─ Branch 2: ∈ closure? [...]                                  ~1 ms
│  └─ ...
│  └─ Branch 5999: ∈ closure? [...]                               ~1 ms
└─ Total: 6000 × 1 ms = 6 sec just for kernel checking
  (Plus elaboration, unification, substitution, ...)
  → Overall: 10-20 minutes

Per-Branch (in parallel): O(500 case nodes per file)
┌─ File 0 kernel checks 500 branches              : 0.5 sec
├─ File 1 kernel checks 500 branches              : 0.5 sec
├─ ... (parallel on 8 cores)
└─ Total per-file: O(500) = 0.5 sec each
  → Amortized across 8 cores: 0.5 sec wall time
  → Much faster!

Batched: O(500 case nodes per batch × 12 batches) in parallel
┌─ Batch 0 kernel checks 500×500 nodes           : 0.5 sec
├─ Batch 1 kernel checks 500×500 nodes           : 0.5 sec
├─ ... (parallel on 8 cores)
└─ Total per-batch: O(250K) = 0.5 sec each
  → 12 batches ÷ 8 cores = 1.5 sec wall time
  → Modest parallelism benefit (not O(1) per batch due to size)
```

---

## 6. I/O Overhead Analysis

```
Monolithic:
├─ 1 .olean file to load             : 1 lookup + 50 MB read = ~100 ms
├─ Other imports (shared defs)       : negligible
└─ Total I/O: ~100 ms (acceptable)

Per-Branch (6000 files):
├─ 6000 .olean files to load         : 6000 × 1 ms = 6 sec (ext4)
│  └─ On APFS: 6000 × 0.1 ms = 600 ms (lazy mmap)
├─ Root assembler imports all 6000   : must stat each file
└─ Total I/O: 6-30 sec overhead (killer on ext4!)

Batched (12 files):
├─ 12 .olean files to load           : 12 × 5 ms = 60 ms
├─ Root assembler imports 12         : very fast
└─ Total I/O: ~100 ms (comparable to monolithic!)
              ← This is why batching wins!
```

---

## 7. Complexity vs. Build Time Trade-off

```
      Build Time (seconds)
            ^
           20│  Monolithic
            │  ✗ Too slow
            │  │
           10│  │
            │  │
            │  │
            5│  │         Per-Branch (6000 files)
            │  │         ✗ I/O overhead kills parallelism
            │  │         │
           2.5│  │         │
            │  │         │
           1.5│  │         Batched (12 files)
            │  │         ✓ Sweet spot
            │  │         │
            0│  └─────────┴─────────────────────→ Code Complexity
                0.1  0.5  1.0  2.0  3.0
                (Low) ← Code Complexity → (High)

  Where:
    - Monolithic: Low code complexity, but unscalable
    - Per-branch: Low code complexity (generator), but I/O overhead
    - Batched: Slightly higher (generator + assembly), but optimal
```

---

## 8. Trust Boundary Comparison

```
Monolithic:
┌────────────────────────────────────────┐
│ Lean 4 kernel verifies all 6000 cases  │ ← Full verification
│ (trustworthy but slow)                 │
└────────────────────────────────────────┘

Per-Branch:
┌────────────────────────────────────────┐
│ Lean 4 kernel verifies each branch     │ ← Full verification
│ (same as monolithic, just parallelized)│
└────────────────────────────────────────┘

Batched:
┌────────────────────────────────────────┐
│ Lean 4 kernel verifies each batch      │ ← Full verification
│ (same as per-branch, just batched)     │
└────────────────────────────────────────┘

External Axiom (fallback):
┌────────────────────────────────────────┐
│ CVC5 verifies SMT certificates         │ ← External harness
│ (weaker trust, but fast)               │
└────────────────────────────────────────┘

Recommendation: Batch proofs (full verification) unless it fails,
then pivot to external axiom (weaker trust, but auditable).
```

---

## 9. Scale Envelope

```
                    Max viable branches (at 250 closure PCs)
                         ↓
         800 │
             │        ┌─ Per-branch
             │        │  (parallelizes)
         600 │        │  ╱╱╱╱╱╱╱
             │        │ ╱╱╱╱╱╱╱
             │ ╱╱╱    │╱╱╱╱╱╱╱
         400 │╱╱╱     ┤╱╱╱╱╱╱╱
             │╱╱╱     │╱╱╱╱╱╱╱
         200 │╱╱╱     │╱╱╱╱╱╱╱
             │╱╱╱ ┌──┴─ Batched (recommended)
             │╱╱╱ │      ┌──pers╱╱╱
             │╱╱╱ │     ╱╱ Monolithic (kernel bottleneck)
         0  ├────┴────╱──────────────→ Branches
             0   2K   6K        10K

- Monolithic: 0-2K branches is OK. 2K-6K breaks badly. >6K unviable.
- Per-branch: Unlimited (6000 = 1-3 min, but I/O overhead grows).
- Batched: Unlimited (6000 = 45 sec, scales linearly).
- External: Unlimited (10+ sec regardless of scale, but weaker trust).
```

---

## 10. Decision Tree

```
START: "I need to prove closure for N branches with M closure PCs"
  │
  ├─ N < 500?
  │   └─ YES: Use monolithic. Simple, fine for small scale.
  │
  ├─ 500 < N < 2000?
  │   └─ YES: Monolithic still OK, but consider batching for future.
  │
  ├─ 2000 < N < 6000?
  │   └─ YES: Use batched approach (12-24 batches).
  │       └─ Batches still timing out?
  │           └─ YES: Reduce batch size to 250 (24 files).
  │           └─ NO: You're good! Proceed.
  │
  ├─ N > 6000?
  │   └─ YES: Definitely use batched. Scale as (N ÷ 500) batches.
  │       └─ Still too slow?
  │           └─ YES: Use external axiom + CVC5 harness.
  │
  └─ END: Build and debug incrementally.
```

---

## Summary Table (All Metrics)

| Metric | Monolithic | Per-Branch (6K) | Batched (12) | Winner |
|--------|-----------|-----------------|------------|--------|
| Full build | 10-20 min | 1-3 min | 45 sec | Batched |
| Incremental | 10-20 min | 1-3 min | 15 sec | Batched |
| Memory peak | 1-2 GB | 400 MB | 800 MB | Per-branch |
| Kernel check | 6 sec (serial) | 6 sec (parallel) | 1.5 sec | Batched |
| File I/O | 100 ms | 6-30 sec | 100 ms | Monolithic ≈ Batched |
| Parallelism | None | Perfect | Perfect | Per-branch ≈ Batched |
| Code complexity | Low | Low | Moderate | Monolithic ≈ Per-branch |
| Trust boundary | Full | Full | Full | All equal |
| Max scale | 2-3K | 100K+ | 100K+ | Per-branch ≈ Batched |
| Debuggability | Hard | Easy | Easy | Per-branch ≈ Batched |
| **OVERALL** | ✗ | ✓ | ✓✓ | **Batched** |

