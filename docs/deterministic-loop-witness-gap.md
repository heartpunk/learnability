# Deterministic Loop Witness Gap

## What is already proved

In `Instances/ISAs/VexWitness.lean` we now have:

- `whileLoopRegionSpec`
- `WhileLoopUnrollBound`
- `whileLoopWitnessSound_of_boundedPathBehavior`
- `whileLoopUnrollBound_of_stabilization`
- `repeatBlockPath_reaches_iterate_of_bodyEffect_mem`
- `boundedWhileCoverage_of_bodyEffect_path`
- `whileLoopUnrollBound_of_stabilization_and_bodyEffect_path`

So the deterministic route now discharges the **coverage** half of loop witness completeness under the simple body-path realizability hypothesis:

```lean
∀ s, summary.bodyEffect s ∈ execBlockPath body s
```

Combined with `stabilization_complete`, this is enough to prove the concrete
`WhileLoopUnrollBound` obligation.

## Remaining wall

This does **not** yet give full `LoopWitnessComplete`.

The missing piece is the **soundness** half:

```lean
LoopWitnessSound (whileLoopRegionSpec ...) body K
```

The theorem we already proved shows that soundness follows from the stronger hypothesis:

```lean
∀ n s s',
  n ≤ K →
  s' ∈ execBlockPath (repeatBlockPath body n) s →
  boundedWhileBehavior summary K s s'
```

This is much stronger than mere body-effect realizability.

## Exact gap

`summary.bodyEffect s ∈ execBlockPath body s` only gives **existence** of one path
realizing the deterministic body effect. It does **not** say:

1. that every output of `execBlockPath body s` equals `summary.bodyEffect s`, or
2. that repeated executions of `body` respect the loop's `continues`/`exits`
   guard discipline.

Those are exactly the facts needed to turn arbitrary outputs of the bounded witness
into real `boundedWhileBehavior` executions.

## What would close the gap

One of these stronger bridge hypotheses is sufficient:

### Option A: exact single-iteration semantics

```lean
∀ s s',
  s' ∈ execBlockPath body s ↔
    s' = summary.bodyEffect s
```

plus a separate theorem that the guard discipline is inherited at the region level.

### Option B: direct bounded-path soundness

```lean
∀ n s s',
  n ≤ K →
  s' ∈ execBlockPath (repeatBlockPath body n) s →
  boundedWhileBehavior summary K s s'
```

This is exactly the hypothesis used by
`whileLoopWitnessSound_of_boundedPathBehavior`.

### Option C: richer witness object

The current `boundedLoopWitness body K` is just repetition of one fixed body path.
If the real loop body has internal branching, a more faithful witness object may need
to range over a family of per-iteration body paths rather than one repeated path.
That would move some of the current soundness burden from theorem hypotheses into the
witness construction itself.

## Recommendation

Do not push the deterministic route further until the intended bridge hypothesis is
chosen explicitly.

At this point the deterministic route is cleanly decomposed as:

- **coverage**: done under stabilization + body-effect path realizability
- **soundness**: still needs a stronger body-path/guard-discipline bridge

That is the exact boundary.
