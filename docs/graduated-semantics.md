# Graduated Semantics: What We Prove At Each Level of Analysis Completeness

## Date: 2026-03-14

## Motivation

The pipeline extracts a grammar from a binary. The abstract framework proves this grammar
is bisimilar to the concrete program (under hypotheses). But bisimulation is the strongest
possible claim — what do we get when the analysis is *incomplete*?

This document maps our framework to van Glabbeek's linear time - branching time spectrum
to give a **graduated semantics**: the precise semantic equivalence we achieve depends on
how complete the analysis is, and we can characterize exactly what level we reach at each
stage.

## Van Glabbeek's Spectrum (1990, 1993)

The linear time - branching time spectrum (van Glabbeek 1990) arranges 11 process
semantics from coarsest to finest:

```
                    bisimulation (B)
                         |
                 2-nested simulation (2S)
                    /              \
     possible futures (PF)    ready simulation (RS)
                    \          /          \
                readiness (R)        simulation (S)
               /            \            /
    failure trace (FT)     (independent)
              |
          failure (F)
              |
      completed trace (CT)
              |
          trace (T)
```

Key structural fact: **simulation (S) and the failure chain (T < CT < F < FT) are
INDEPENDENT branches.** They merge at ready simulation (RS).

Van Glabbeek 1993 extends this to 155 notions including silent moves, but the 1990
hierarchy suffices for our analysis.

## Direction of Approximation

### Critical insight: we OVER-approximate, not under-approximate

ISA-precise symbolic execution at each step gives **complete branching**:

- Every conditional branch is explored both ways
- Path conditions partition the concrete state space
- Every concrete state satisfies at least one branch's path condition
- We can have EXTRA branches (from path conditions that are unsatisfiable but not provably
  so), but we NEVER miss branches

So the symbolic model **over-approximates** the concrete system:

- `Traces(concrete) ⊆ Traces(model)` — model has all concrete traces plus possibly extras
- `Failures(model) ⊆ Failures(concrete)` — model has FEWER failures (more options = fewer
  refusals)
- **`concrete ≤_sim model`** — model can simulate concrete (the useful direction)
- Model refusals are VALID: if the model says "impossible after state σ", it IS impossible

### Incompleteness = computational depth, not branching

The over-approximation is about branching width at each step. Incompleteness in our system
is about **compositional depth**: how many rounds of branch-set composition we compute.

- Single-step symbolic execution: COMPLETE (all branches explored)
- Multi-step composition: computationally bounded — we may not iterate to fixpoint
- The question is HOW MANY rounds, not whether we miss branches within a round

## Compositional Symbolic Execution (Voogd et al.)

Voogd,";"; Bockenheimer, and Huisman ("Compositional Symbolic Execution Semantics," 2025)
prove that symbolic execution is **exact** — both correct and complete:

- **Theorem 2**: Single-step symbolic execution is correct and complete
- **Lemma 10**: Composition preserves correctness and completeness (Coq-mechanized)
- **Corollary 2**: Partial exploration is SOUND (correct but potentially incomplete)

Their composition formula is exactly ours:
```
sub = σ₁ ∘ σ₂
pc  = φ₁ ∧ σ₁(φ₂)
```

This is the formula in `composeBranchSets` (`Core/Composition.lean`).

### Implication for graduated claims

Composition doesn't introduce error. If g is exhaustively analyzed (fixpoint reached,
model bisimulates concrete-g), then `compose(f, model-g) = compose(f, concrete-g)`.
This holds because composition only depends on the semantic content of branches, and
Lemma 10 says composition preserves exactness.

This means partial exploration gives **simulation**, not merely failure trace semantics.
The H6 compositionality hypothesis from the STS1 framework is confirmed by Voogd et al.

## CVC5 Contribution

CVC5 is sound AND complete for QF_BV (quantifier-free bitvector theory). Our SMT queries
are all QF_BV. Therefore CVC5 introduces **no approximation** in our setting:

- If CVC5 says "unsat" → the path condition IS unsatisfiable
- If CVC5 says "sat" → the path condition IS satisfiable
- CVC5 never returns "unknown" for QF_BV (decidable theory)

The only trust boundary is CVC5's implementation correctness, not its theoretical
completeness. This is what lean-smt addresses: kernel-verified proof reconstruction
eliminates even the implementation trust.

## The Graduated Claim

### Level 1: Complete analysis (fixpoint reached) → BISIMULATION

When the pipeline reaches stabilization (branch set stops growing under composition):

- The branch set is a fixpoint of composition
- `BranchClassesStable` holds (`VexDispatchLoop.lean`)
- `BranchingLoopWitnessComplete` follows (`VexWitness.lean`)
- The extracted model is adequate: `pipeline_extracted_model_adequate` (`VexPipelineBridge.lean`)
- **Result: bisimulation between extracted LTS and concrete system**

This is what we achieve on Tiny C (stabilization in 2 rounds, 30ms).

### Level 2: Partial exploration (not at fixpoint) → SIMULATION

When we compute N rounds of composition but haven't reached fixpoint:

- By Corollary 2 (Voogd et al.), partial exploration is sound
- We have `concrete ≤_sim model_N` (the model at round N can simulate concrete)
- Every concrete trace is a trace of the model
- The model may have extra traces (from branches not yet composed away)
- **Result: simulation preorder, concrete simulated by model**

Practical meaning: the extracted grammar is an UPPER BOUND on the parser's language.
If the model says "token X is impossible after state σ", it IS impossible. The grammar
may accept extra strings, but its refusals are correct.

### Level 3: Solver limitations → SIMULATION (unchanged)

Since CVC5 is complete for QF_BV, solver limitations don't weaken the guarantee beyond
Level 2. An "unknown" from a different solver would create extra branches (unsatisfiable
PCs not pruned), but CVC5 never returns "unknown" for our queries.

If a different solver were used (one that could return "unknown"):
- Extra branches = over-approximation = still simulation
- Model refusals still valid
- The semantic level doesn't drop below simulation

### Level 4: ISA trust boundary (pyvex) → CONDITIONAL

All levels above are conditional on pyvex faithfully lifting x86-64 to VEX IR. This is
not a semantic weakening — it's an axiomatic boundary. The bisimulation/simulation claims
hold *relative to* the ISA semantics pyvex provides.

Path to removing this boundary: ISA-precise symbolic execution (cf. Park et al. 2025,
"Accurate and Extensible Symbolic Execution of Binary Code based on Formal ISA
Semantics"). With a formally verified ISA spec, the trust boundary narrows to "the
hardware implements the ISA spec."

## Readiness and Failure Semantics

We do NOT claim readiness semantics. Readiness requires knowing the EXACT set of enabled
actions at each state. Our model provides a possibly-too-large enabled set (over-
approximation of branches). So:

- We know what IS possible (any concrete action is in our model's enabled set)
- We might think more is possible than actually is (extra branches)
- This gives us simulation, not readiness

We DO get **failure information** from simulation: if the model refuses action X after
state σ (no branch with X in the enabled set), then the concrete system also refuses X.
Model refusals are valid refusals. But this is a consequence of simulation, not a separate
failure-semantics claim.

## Practical Meaning for Grammar Extraction

### Over-approximate grammar

The extracted grammar generates a superset of the parser's actual language:

- **False positives possible:** grammar may accept strings the parser rejects
- **False negatives impossible:** grammar never rejects strings the parser accepts
- **Refusals correct:** "token X impossible after context σ" is TRUE of the parser

### Applications

- **Fuzzing:** Grammar-generated inputs either test happy paths (valid inputs) or error
  handling (inputs the grammar accepts but the parser may reject). Both are useful for
  testing.
- **Spec recovery:** Grammar is an upper bound on the parser's language, with correct
  impossibility judgments. Over-approximation means the recovered spec is conservative.
- **Security analysis:** If the grammar says "no path reaches state X", there genuinely
  is no path. Sound for reachability denial.

## Connection to Existing Proofs

| Component | File | Status |
|-----------|------|--------|
| Branch composition | `Core/Composition.lean` | Proved (0 sorry) |
| Convergence | `Learnability/Convergence.lean` | Proved (0 sorry) |
| BranchClassesStable | `VexDispatchLoop.lean` | Proved (0 sorry) |
| Witness completeness | `VexWitness.lean` | Proved (0 sorry) |
| Pipeline bridge | `VexPipelineBridge.lean` | Proved (0 sorry, 0 axiom) |
| Simplification soundness | `VexSimplificationSoundness.lean` | Proved (0 sorry, 0 axiom) |
| Dedup soundness | `VexDedupSoundness.lean` | Proved (0 axiom) |
| hStep for dispatch | `VexPipelineBridge.lean` | Proved |
| ISA instance (9 laws) | `VexSummaryISA.lean` | Proved |

The pipeline bridge takes hypotheses (hStep, hAllBlocks, h_contains, h_closed) that the
pipeline validates empirically but doesn't produce proof objects for. These are the formal
gap — the pipeline COMPUTES the right answer but doesn't CERTIFY it.

## Path to Certification

Two concrete steps would substantially narrow the gap:

1. **Prove `toSMTLib` faithfully encodes `SymPC`.** `toSMTLib` is now total (`def`, not
   `partial def`). A proof that it faithfully encodes `SymPC` into SMT-LIB would allow
   lean-smt to verify CVC5's answers at the kernel level, eliminating the CVC5
   implementation trust boundary.

2. **ISA-precise symbolic execution.** Replace pyvex with a formally verified ISA
   specification (e.g., Sail for ARM/RISC-V, or a custom Lean ISA model). This narrows the
   trust boundary to the hardware specification.

## References

- van Glabbeek, R.J. (1990). "The linear time - branching time spectrum." CONCUR '90.
  [Zotero: W9KIUEMT]
- van Glabbeek, R.J. (1993). "The linear time - branching time spectrum II: The semantics
  of sequential systems with silent moves." CONCUR '93. [Zotero: 4Q9TGWI3]
- Voogd, L.; Bockenheimer, K.; Huisman, M. (2025). "Compositional Symbolic Execution
  Semantics." [Coq-mechanized proofs]
- Park, S. et al. (2025). "Accurate and Extensible Symbolic Execution of Binary Code
  based on Formal ISA Semantics." [Zotero: DTCAX9ED]
- Pointner, S. et al. (2025). "Attributed Grammar Mining from Parsers."
  [Zotero: closest prior art]
