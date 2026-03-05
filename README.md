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

## The effective observability bound

The fourth implicit precondition mentioned above is worth making explicit, because it is where most real applications fail or succeed.

The three formal preconditions — finite behavioral structure, identifiable observations, sound oracle — are satisfiable for almost any compiled system. The hard constraint is practical: you need an oracle that can *construct* distinguishing experiments, not just confirm them. The oracle must be productive.

For Level 0 systems (byte-stream input: parsers, terminal emulators, protocol implementations), productive oracle construction is mechanically achievable. KLEE with symbolic stdin explores all branches driven by input bytes. The observation channel is the system boundary itself — an I/O interface you can point at. Locating the relevant dispatch functions is engineering (PDG backward slice, then targeted symbolic execution), but *what* to observe is unambiguous.

This maps directly to the OGIS (oracle-guided inductive synthesis) setting. The oracle does not just say yes/no — it constructs the concrete distinguishing input. For KLEE at Level 0: if states `s` and `s'` are conflated by the current projection, KLEE can find the stdin bytes that drive them to different successors. Reducible control flow (no computed gotos, no self-modification) ensures KLEE's CFG reconstruction is sound, which is the practical precondition for productive oracle construction.

For systems where the input channel cannot be mechanically identified — type checkers (whose "input" is an AST produced by a prior stage), effect systems (whose domain is woven through multiple subsystems), staged compilers — the effective observability problem is harder. The formal theorem still applies: finite behavioral structure exists, identifiable observations exist, a sound oracle exists in principle. The question is whether you can construct that oracle without external knowledge of the domain's boundaries. At Level 1 (internal representations), oracle construction requires the prior stage's extracted model as a precondition — the extracted grammar constrains the symbolic AST space, preventing spurious paths. At Level 2 (cross-cutting concerns), no clean input channel exists even at the representation level, and construction requires domain knowledge or human judgment.

Effective observability is the fourth implicit precondition. The theorem guarantees that if you satisfy it, extraction converges. Whether you can satisfy it for a given system is the practical research question.

## The grammar conformance / slice thickness bound

The theorem guarantees that iterative refinement converges and the result is faithful. It does not guarantee the result is *useful*. A second bound — slice thickness — brackets when extraction gives you something meaningful rather than something technically correct but practically empty.

`extraction_cost_bound` puts an upper bound on the dimensions tracked: `|extractionDims| ≤ |Finset.univ|`. Extraction always converges within the full dimension space. The useful regime is where the tracked dimensions are much smaller than all possible dimensions:

```
|extractionDims| ≪ |Finset.univ|
```

When this holds, you have extracted a *thin slice* — a compact behavioral model capturing the domain's actual structure, not the full complexity of the implementation. A grammar extracted from a parser, for example, tracks dimensions corresponding to grammatical distinctions (token type, nesting depth, operator precedence) while ignoring the parser's memory allocator, error recovery strategy, and I/O buffering.

Grammar conformance is what makes thin slices possible. A program's dispatch structure *conforms* to a domain's logical structure when the code's spatial organization reflects the domain's decomposition: related handlers cluster in nearby code regions, input features map cleanly to dispatch branches, data flows along paths that match the domain's compositional structure. A recursive descent parser conforms to the grammar it implements — each nonterminal has a recognizable handler, each syntactic construct drives a distinct branch. This is not a property of parsers specifically; it is a general property of well-structured implementations of any domain with clean logical structure.

When conformance holds, the clustering heuristics work: KLEE paths through the same CDG region correspond to the same handler, path conditions over the same DDG edges correspond to the same dimension. The extracted model maps back to the domain's logical decomposition. This is the setting where extraction is *interesting*.

When conformance fails — when a single handler implements multiple logical concerns, when dispatch is over implementation artifacts rather than domain features — extraction still converges, but `|extractionDims|` approaches `|Finset.univ|`. You have learned the whole system, not the domain. The result is technically sound (the projected oracle is correct) but practically useless: the model does not decompose along the domain's logical boundaries, so it cannot be interpreted as a grammar, a type system, or a protocol specification. It is just a compressed record of all observed paths.

The slice thickness bound brackets the practical applicability of the technique: extraction is useful when `|extractionDims| ≪ |Finset.univ|`, and this happens when the observation dimensions are chosen to match the domain's actual structure, not the implementation's incidental organization. Choosing those dimensions well is the engineering problem that grammar conformance, PDG annotation, and domain knowledge all address.

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
