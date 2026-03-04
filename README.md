# Learnability

Imagine you're reverse-engineering a C program that parses JSON. The program has hundreds of internal states, but the JSON grammar only needs a handful of behavioral distinctions. If you can observe the program's state and query its behavior — instrument it, run a symbolic executor against it, whatever gets you the observations — then there is a procedure that discovers which distinctions matter. It finds pairs of states that your current model conflates but that behave differently, refines the model, and repeats. When no more distinguishing pairs exist, the model is faithful.

The real contribution is that this is possible *at all*. This is a Lean 4 formalization proving that any system with finite behavioral structure, identifiable observations, and a sound oracle admits faithful extraction via iterative refinement (`extraction_exists` in `Learnability.lean`). The algorithm is abstract — it proves a faithful model exists and that refinement converges, but building the instrumentation and oracle for your specific system is on you. 0 sorries.

## Reading order

The same idea is formalized twice — once concretely for labeled transition systems (files 1-3), once abstractly for any observable system (files 4-5).

**Concrete (LTS) chain:** `LTS.lean` → `ConditionalSimulation.lean` → `Convergence.lean`

- `LTS.lean` — labeled transition systems, simulation, traces. Start here for the vocabulary.
- `ConditionalSimulation.lean` — projections, oracle conditions (soundness/realizability/uniformity), simulation theorems. The Galois connection between concrete and projected step relations.
- `Convergence.lean` — iterative dimension refinement converges to a fixpoint where the oracle is sound and non-controllable transitions are invisible. The carving metaphor: each iteration splits an equivalence class that the current projection conflates.

**General framework:** `Learnability.lean` → `CoinductiveBisimulation.lean`

- `Learnability.lean` — the general framework, independent of the LTS chain (imports only Mathlib). Works for any `behavior : State → Label → State → Prop` — not just transition systems but typing judgments, parse relations, effect propagation. Contains the main theorem and all refinement machinery.
- `CoinductiveBisimulation.lean` — capstone: upgrades simulation to bisimulation when the oracle is complete. Both Milner (union-of-bisimulations) and coinductive encodings, with equivalence proof.

## Building

Requires Lean 4 + Mathlib.

```
lake build
```
