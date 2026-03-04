# Learnability

Lean 4 formalization of a general framework for extracting faithful behavioral models from observable systems via iterative dimension refinement.

## Files

- `LTS.lean` — labeled transition systems, simulation, traces
- `ConditionalSimulation.lean` — projection, oracle conditions, simulation theorems
- `Convergence.lean` — iterative dimension refinement, fixpoint convergence
- `Learnability.lean` — general framework (independent of LTS chain, imports only Mathlib)
- `CoinductiveBisimulation.lean` — bisimulation via learnability (capstone)

## Building

Requires Lean 4 + Mathlib.

```
lake build
```
