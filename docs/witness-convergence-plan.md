# Witness-First Convergence Plan

## Core Decision

We should proceed witness-first, but I would **not** make the first `Region` object a CFG/inside/exit structure.

That would front-load the same closure/staying-inside machinery we decided to avoid.

Instead, the first `Region` should be **extensional**: just enough semantics to state what observed behavior the subsystem has. Then path-family witnesses and convergence theorems connect to that semantic object. Structural/CFG packaging can come later.

So the plan splits into two theorem layers:

1. **Witness semantics**: if a finite path family is complete for a region, then the extracted summary family is an adequate model of that region.
2. **Witness existence**: for important regions (especially loops), show that a finite complete witness exists, using stabilization / bounded unrolling / finite-state arguments.

That keeps the open convergence problem isolated as a witness-existence theorem, not mixed into the definition of subsystem adequacy.

## What I Agree With

I agree with your reformulation:
- witness completeness is the convergence problem in better clothes
- that is good, because now it is stated over objects we already know how to reason about
- finite path families are the right first witness
- circular coinduction / bounded unrolling should later discharge witness completeness for loops

## Where I Disagree

I would not define `Region` minimally as:
- program
- entry
- exit
- staying-inside predicate

not yet.

That is already the beginning of CFG semantics, and it introduces structural questions before we need them.

Instead, define:

```lean
structure Region (Reg Obs : Type) [DecidableEq Reg] [Fintype Reg] where
  Relevant : ConcreteState Reg -> Prop
  observe  : ConcreteState Reg -> Obs
  DenotesObs : ConcreteState Reg -> Obs -> Prop
```

This is the right first region object because it says only what the subsystem *means* observationally.

Then witness completeness is a theorem about that meaning, not about one specific structural representation.

## Theorem Layer 1: Witness Semantics

### Path-family witness completeness

```lean
def WitnessComplete
    {Reg Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths : Finset (List (Block Reg))) : Prop :=
  forall s o,
    ExecPathFamilyDenotesObs R.Relevant R.observe paths s o <->
      R.DenotesObs s o
```

This says: the finite path family covers exactly the region's observed behavior.

### Extracted model adequacy from witness completeness

```lean
theorem extractedModel_of_witnessComplete
    {Reg Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths : Finset (List (Block Reg)))
    (hcomplete : WitnessComplete R paths) :
    forall s o,
      VexModelDenotesObs R.Relevant R.observe (lowerPathFamilySummaries paths) s o <->
        R.DenotesObs s o
```

Proof shape:
- use `lowerPathFamilySummaries_denotesObs_iff_execPathFamily`
- then compose with `hcomplete`

This is the first theorem that actually says:
- if you can witness a subsystem by a finite path family,
- then the extracted symbolic model is adequate for that subsystem.

That is the core extractibility theorem in witness form.

### Optional corollary: model equivalence of two complete witnesses

```lean
theorem completeWitnesses_modelEq
    {Reg Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (paths1 paths2 : Finset (List (Block Reg)))
    (h1 : WitnessComplete R paths1)
    (h2 : WitnessComplete R paths2) :
    VexModelEq R.Relevant R.observe
      (lowerPathFamilySummaries paths1)
      (lowerPathFamilySummaries paths2)
```

This is useful because it says witness choice does not matter up to semantic equivalence.

## Theorem Layer 2: Loop Regions and Witness Existence

Now instantiate `Region` for loops.

### Loop region semantics

This should be extensional first:

```lean
def LoopRegion
    {Reg Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (Relevant : ConcreteState Reg -> Prop)
    (observe : ConcreteState Reg -> Obs)
    (program : Program Reg)
    (body : Block Reg)
    (entryPred : ConcreteState Reg -> Prop)
    (exitPred  : ConcreteState Reg -> Prop) :
    Region Reg Obs :=
  { Relevant := Relevant
    observe := observe
    DenotesObs := ... }
```

The exact `DenotesObs` can initially be based on the program/path machinery already proved, not on a full general CFG closure story.

### Bounded witness family for loops

```lean
def boundedLoopWitness
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (body : Block Reg) (K : Nat) : Finset (List (Block Reg)) :=
  -- all block paths corresponding to up-to-K loop iterations
  ...
```

This does not need to be perfect yet; it just needs to be the finite family we later prove complete.

### Witness completeness from a semantic bound

```lean
theorem loopWitnessComplete_of_unrollBound
    {Reg Obs : Type} [DecidableEq Reg] [Fintype Reg]
    (R : Region Reg Obs)
    (body : Block Reg)
    (K : Nat)
    (hbound : forall s o,
      R.DenotesObs s o ->
        ExecPathFamilyDenotesObs R.Relevant R.observe (boundedLoopWitness body K) s o) :
    WitnessComplete R (boundedLoopWitness body K)
```

This theorem isolates the real problem:
- produce the bound `K`
- then extractibility follows mechanically

## Theorem Layer 3: Where K Comes From

This splits cleanly into two routes.

### Route A: Symbolic stabilization / circular coinduction

```lean
theorem loopUnrollBound_of_stabilization
    ...
    (hstab : loopBranchSet K = loopBranchSet (K+1)) :
    forall s o,
      LoopRegion ... .DenotesObs s o ->
        ExecPathFamilyDenotesObs Relevant observe (boundedLoopWitness body K) s o
```

This is the direct route from the existing circular coinduction machinery.

### Route B: Finite-state orbit argument

```lean
theorem loopUnrollBound_of_finite_effect_convergence
    [Fintype (ConcreteState Reg)]
    ... :
    exists K,
      forall s o,
        LoopRegion ... .DenotesObs s o ->
          ExecPathFamilyDenotesObs Relevant observe (boundedLoopWitness body K) s o
```

This is the concrete-state finiteness route.

Important point:
- this theorem is not yet about raw symbolic stabilization
- it is about existence of a finite complete witness
- that is the right reformulation

## Theorem Layer 4: Return to Main Goal

Once the above exists, the higher-level theorem shape becomes:

```lean
theorem loopExtractible_of_finiteCompleteWitness
    (hcomplete : WitnessComplete (LoopRegion ...) paths) :
    forall s o,
      VexModelDenotesObs Relevant observe (lowerPathFamilySummaries paths) s o <->
        LoopRegion ... .DenotesObs s o
```

Then combine it with a witness-existence theorem:

```lean
theorem loopExtractible_of_stabilization
    (hstab : loopBranchSet K = loopBranchSet (K+1)) :
    forall s o,
      VexModelDenotesObs Relevant observe
        (lowerPathFamilySummaries (boundedLoopWitness body K)) s o <->
          LoopRegion ... .DenotesObs s o
```

or with the finite-state route:

```lean
theorem loopExtractible_of_finite_state
    [Fintype (ConcreteState Reg)] :
    exists paths,
      forall s o,
        VexModelDenotesObs Relevant observe (lowerPathFamilySummaries paths) s o <->
          LoopRegion ... .DenotesObs s o
```

This is much closer to the real extractibility thesis.

## Commit Plan For A Fresh Session

### Commit 1
`document witness-first convergence plan`
- this doc only

### Commit 2
`add extensional region and witness completeness definitions`
- `Region`
- `WitnessComplete`
- `extractedModel_of_witnessComplete`
- optional `completeWitnesses_modelEq`

### Commit 3
`add loop region and bounded witness skeleton`
- `LoopRegion`
- `boundedLoopWitness`
- theorem statement stubs only if needed for orientation

### Commit 4+
choose one route:
- stabilization route first, or
- finite-state route first

My recommendation is the stabilization route first, because it stays closest to the circular coinduction machinery we already spent time on.

## Why This Is The Right Split

This gives us:
- one theorem family about what a complete witness *buys you*
- a separate theorem family about when such a witness *exists*

That is the cleanest way to keep the project honest.

The witness-completeness theorem is extractibility.
The witness-existence theorem is convergence.

Same problem in better clothes, but now the clothes line up with the objects we already proved things about.
