# Future Direction: GP + Dependent Types + S2E for Provably Adequate Stub Synthesis

## Origin (2026-03-10)

Arose from Phase F stub problem (external calls in dispatch-loop analysis) + reading AutoStub
(arxiv 2509.08524v1: genetic programming for symbolic execution stubs).

## The Idea

**AutoStub:** GP over programs, fitness = empirical I/O matching. 90% accuracy for 55% of
functions. Approximate by construction — no formal guarantees.

**Extension:** GP over DEPENDENTLY TYPED TERMS where fitness = type checker.
- A candidate that type-checks IS proved adequate — proof is the term itself
- Adequacy is PURPOSE-SPECIFIC: not "model malloc exactly" but "model malloc adequately
  for this specific analysis" — much weaker and more relevant spec
- S2E on the real function produces `Branch Sub PC` summaries (already in our framework's
  language) that define what "adequacy for this analysis" means concretely
- For large external functions: GP finds a compact typed term covering S2E-sampled traces
- For small ones: S2E alone suffices, no GP needed

**Connection to this codebase:** The `Branch Sub PC` type and `BranchModel.Sound`/`Complete`
predicates are exactly the right language for expressing stub adequacy specs.
A stub `t : CompTree Sub PC` is adequate for analysis A iff:
  `BranchModel.Sound isa (denot isa t) A.behavior`
This is a Lean proposition — it's what the GP candidates need to satisfy.

## Status

**PARKED.** Current Phase F uses handcrafted calling-convention stubs (provably adequate by
inspection of the ABI spec). Return to this after the dispatch-loop pipeline is working.

Could be its own paper: "Proof-Synthesizing Symbolic Stubs via Dependent Types and S2E"

## References
- AutoStub paper: arxiv 2509.08524v1
- S2E available in the pipeline
- Related: Fare's thesis §4 — implementation as partial functor; stub adequacy = partiality
