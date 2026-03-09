# Next Tier Ladder Plan

Current ladder reaches Tier 6 with a real while-based loop witness example.

## Tier 7: Branching Loop Witness

Goal: first end-to-end example of the branching loop-witness route.

Target theorem:
- `whileBranchingLoopWitnessComplete_of_branchClassesStable`

Shape:
- use an already-supported branching body (no new opcodes)
- provide a tiny `bodyPaths` family with internal branching
- prove the required branch-class stability/soundness hypotheses for a toy case
- conclude `BranchingLoopWitnessComplete` and the extracted-model payoff

Constraint:
- no new VEX semantic surface
- theorem-focused only

## Tier 8: Body Refinement STS1

Goal: first toy example through the `Refinement.lean` STS1 pipeline.

Target theorem:
- `vexBodyRefinementBisimulation`
- and the corresponding card-bound corollary

Shape:
- pick a small already-supported body model
- instantiate `SemClosed`
- show the actual `CrossBisimulation` result through the refinement pipeline

Constraint:
- no new VEX semantic surface
- exercise the semantic-closure replacement for `h_closed`

## Tier 9: Witnessed Subsystem

Goal: first subsystem-level example using a finite path-family witness.

Target theorem family:
- `WitnessComplete`
- `extractedModel_of_witnessComplete`
- optionally `completeWitnesses_modelEq`

Shape:
- define a tiny subsystem region
- provide two equivalent complete witnesses if possible
- show extracted-model adequacy and witness-equivalence consequences

Constraint:
- do not collapse this into Tier 8
- keep it about witness packaging, not new opcodes

## Commit discipline

- one plan commit first
- then Tier 7 commits only
- then Tier 8 commits only
- then Tier 9 commits only
- no commit may mix multiple tiers
