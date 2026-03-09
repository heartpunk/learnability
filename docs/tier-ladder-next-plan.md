# Next Tier Ladder Plan

Current ladder reaches Tier 6 with a real while-based loop witness example.

## Revised order

The original next step was a branching loop-witness tier. That attempt turned out to
pull in too much incidental proof complexity for too little new confidence. The value
was collapsing toward a smoke test instead of a meaningful new theorem layer.

So the next real tier is now the refinement/STS1 path.

## Tier 7: Body Refinement STS1

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

## Tier 8: Witnessed Subsystem

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
- do not collapse this into Tier 7
- keep it about witness packaging, not new opcodes

## Tier 9: Branching Loop Witness (revisit later)

Goal: first real example of the branching loop-witness route.

Target theorem:
- `whileBranchingLoopWitnessComplete_of_branchClassesStable`

Status:
- deferred for now
- the first attempt showed that a meaningful example here wants a better-shaped
  branching loop than the minimal toy currently available
- revisit after the refinement tier and witnessed-subsystem tier are in place

## Commit discipline

- one plan-update commit first
- then Tier 7 commits only
- then Tier 8 commits only
- Tier 9 is deferred
- no commit may mix multiple tiers
