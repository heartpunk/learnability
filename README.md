# Learnability

Most software has no formal specification. Not "the spec is hard to find" — no spec was ever written. The implementation is the only source of truth. This is a Lean 4 formalization proving that for a broad class of systems, a faithful behavioral model can always be extracted from the implementation via iterative refinement.

The procedure: observe the system's state, query its behavior (via symbolic execution, instrumentation, or whatever gets you the observations), and look for pairs of states your current model treats as equivalent but that behave differently. Each such pair reveals a missing distinction. Add it, repeat. When no more distinguishing pairs exist, the model is faithful. The central theorem (`extraction_exists`) proves this process always terminates and the result is always sound.

## What the theorem requires

Three preconditions, formalized as `LearnabilityPreconditions`:

1. **Finite behavioral structure.** The observation space is finite — there are finitely many dimensions along which states can differ. True for any finite-memory machine.
2. **Identifiable observations.** Observations distinguish relevant states. For any type with decidable equality, this is trivially satisfiable (`identifiable_indicator`).
3. **Sound oracle.** Every real behavior has an oracle witness — something that confirms "yes, this transition can happen." Symbolic execution (KLEE, angr) provides this for compiled code.

A fourth implicit precondition — **effective observability** — is the hard unsolved problem: instrumenting the right state at the right granularity. The theorem guarantees convergence *if* you solve that. Whether you can solve it for a given system is the practical question.

## Where it works, where it doesn't

The framework covers systems where the behavioral structure exists in the implementation at analysis time: recursive descent parsers, bytecode interpreters (CPython, not V8), terminal emulators, type checkers, protocol implementations. The dispatch structure — which input drives which behavior — is static in the binary.

It does not yet cover systems where earlier computation produces later behavioral structure: JIT compilers, substantive macro expanders, dependent type elaborators. These share a common structure — computation stages that generate the dispatch structure for subsequent stages — and require cross-stage provenance tracking that this framework does not formalize. This is an open research direction, not a gap we're ignoring. See the literature review notes for the relevant formalisms (Davies & Pfenning modal types, Flatt scope sets, Brady elaboration).

## What's proved

All theorems, no sorries. 616 build jobs.

- **`extraction_exists`** — the main theorem. Given the three preconditions, iterative refinement produces a dimension set where the projected oracle is sound and all behavior is controllable.
- **`extraction_at_fixpoint`** — the same result for any fixpoint of `refineStep`, not just the one discovered by iteration.
- **`exact_extraction`** — with a complete oracle (biconditional with behavior), the projection is also injective on relevant states, giving bisimulation.
- **`extraction_cost_bound`** — refinement terminates in at most |Dim| iterations.
- **`extractionDims_each_dim_witnessed`** — every tracked dimension has a concrete certificate: the pair of states and label that caused it to be added.
- **Coinductive bisimulation** — `BisimilarCo` encoding with equivalence to the Milner (union-of-bisimulations) definition.

## Reading order

The same idea is formalized twice — once concretely for labeled transition systems (files 1-3), once abstractly for any observable system (files 4-5).

**Concrete (LTS) chain:** `LTS.lean` → `ConditionalSimulation.lean` → `Convergence.lean`

- `LTS.lean` — labeled transition systems, simulation, traces. The vocabulary.
- `ConditionalSimulation.lean` — projections, oracles, the Galois connection between concrete and projected behavior. Proves simulation from oracle soundness + projection uniformity.
- `Convergence.lean` — iterative refinement converges to a fixpoint. Each iteration splits an equivalence class the current projection conflates.

**General framework:** `Learnability.lean` → `CoinductiveBisimulation.lean`

- `Learnability.lean` — the general framework (imports only Mathlib). Works for any `behavior : State → Label → State → Prop` — transitions, typing judgments, parse relations, effect propagation. All refinement machinery and main theorems.
- `CoinductiveBisimulation.lean` — upgrades simulation to bisimulation when the oracle is complete.

**Bridge:** `LearnabilityConvergence.lean` — connects the two chains.

## Building

Requires Lean 4 (v4.27.0) + Mathlib.

```
lake build
```
