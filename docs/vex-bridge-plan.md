# VEX Bridge Plan

## Goal

Make the three semantic views of the current VEX fragment explicit and force them to stay aligned:

```text
raw VEX syntax
    | \
    |  \
    |   \
    |    \
    |     v
    |   symbolic summaries
    |         |
    v         v
concrete successor relation
```

The requirement is that the triangle commute:

- executing raw syntax concretely
- lowering raw syntax to summaries
- interpreting summaries concretely

must describe the same concrete behavior.

## The Three Views

### 1. Raw syntax

This is the VEX frontend representation in [Instances/ISAs/VexISA.lean](../Instances/ISAs/VexISA.lean):

- `Expr`
- `Cond`
- `Stmt`
- `Block`

This view exists to stay close to lifted VEX/pyvex.

### 2. Symbolic summaries

This is the ICTAC-style summary algebra in:

- [Instances/ISAs/VexSummary.lean](../Instances/ISAs/VexSummary.lean)
- [Instances/ISAs/VexLowering.lean](../Instances/ISAs/VexLowering.lean)

The key object is a finite family of `(σ, φ)` summaries:

- `σ`: symbolic transformer over machine state
- `φ`: path condition / guard

This view exists to compose symbolically and plug into `SymbolicISA`.

### 3. Concrete behavior

This is the executable behavior of the raw block on concrete states:

- `execBlock`
- `execBlockSuccs`

This view exists to check the model against real executions and against `angr`.

## Primary Theorem Family

The bridge should be made explicit as a named theorem family.

### Soundness

Every concrete successor of a raw VEX block is represented by some enabled lowered summary.

Current shape already exists for the implemented block fragment:

- `lowerBlockSummaries_sound`

### Completeness

Every enabled lowered summary corresponds to a concrete successor of the raw VEX block.

Current shape already exists for the implemented block fragment:

- `lowerBlockSummaries_complete`

### Executable equality (derived, where practical)

For executable finite fragments, derive an extensional equality statement:

```text
execBlockSuccs block input
=
{ output | ∃ summary ∈ lowerBlockSummaries block,
    Summary.enabled summary input ∧
    Summary.apply summary input = output }
```

This should be treated as a convenience corollary of soundness + completeness, not the fundamental theorem.

## Priority Order

### Phase 0: tiny placeholder equality, only if needed

If one small equivalence notion is needed to make theorem statements readable during the bridge work, add only the weakest placeholder needed.

This is not the canonicalization project.
It is only a local aid for theorem formulation.

### Phase 1: make the triangle explicit

The next serious theory task is to make the three-way commuting triangle explicit.

Deliverables:

1. A dedicated bridge file, probably:
   - `Instances/ISAs/VexBridge.lean`
2. Move or re-export the current lowering/correctness results there.
3. State the triangle as a deliberate architecture, not just a pile of lemmas.
4. Make new VEX feature additions pay the bridge proof tax.

### Phase 2: tighten the discipline around feature growth

Once the bridge file exists, the rule becomes:

A new VEX constructor or extractor-supported feature is incomplete unless it updates all three of:

- concrete syntax/execution
- lowering to summaries
- bridge theorems

That rule should be documented and used as the merge gate.

### Phase 3: only then do real canonicalization / quotient work

After the triangle is stable, define the right convergence object over summaries.

That is where summary equality, normalization, or quotienting properly belongs.

## Immediate Concrete Work

### Commit-sized step A

Refactor existing block correctness lemmas under a named bridge module.

Target:

- preserve current theorem strength
- no semantic redesign
- only improve structure and explicitness

### Commit-sized step B

Add one derived theorem expressing set-level agreement between:

- `execBlockSuccs`
- lowered-summary denotation

for the current fragment.

### Commit-sized step C

Document the feature gate:

A new VEX feature is not done until:

1. raw syntax/concrete exec exists
2. lowering exists
3. bridge proofs exist
4. at least one direct example or `angr`-backed fixture exists

## Coordination Rules for Parallel Work

The future coverage-max workspace may:

- add fixtures
- widen corpus within currently supported semantics
- improve the extractor for already-supported semantic categories

The coverage-max workspace must stop and ask for coordination if it needs to:

- add a new `Expr`, `Cond`, `Stmt`, or `Reg` constructor
- modify `VexSummary`
- modify `VexLoweringCorrectness`
- change summary representation
- touch `Core/` or `Learnability/`
- alter the fixture JSON schema

## Why This Comes Before Coverage-Max

Without this bridge discipline, coverage growth is dangerous:

- it can push the extractor ahead of semantics
- or push semantics ahead of proofs
- or push proofs ahead of the actual reference behavior

The triangle is the guardrail that makes unsupervised coverage expansion safe enough to delegate.
