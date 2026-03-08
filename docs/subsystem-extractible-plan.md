# SubsystemExtractible Plan

## Goal

Define and prove the first honest subsystem-level extractibility theorem on top of the completed VEX path/program extractibility stack.

This first version is intentionally scoped to a **finite path-family subsystem** rather than an arbitrary CFG. The point is to package the current block/path machinery into a real subsystem statement without skipping over the semantic witness we still need.

## Meaning

A subsystem should mean:
- a scoped fragment of lifted code,
- with an interface,
- whose extracted symbolic model is semantically adequate for the concrete behavior visible at that interface.

For the first version, the scope witness is a **finite family of valid block paths**.

So the theorem is not yet:
- "all executions staying inside a CFG are extractible"

It is:
- "if a subsystem is witnessed by a finite family of valid entry-to-exit lifted paths, then the extracted summaries of those paths form an adequate model of the subsystem"

That is the right first packaging theorem because it uses only objects we already know how to relate soundly.

## Core Objects

### 1. Path-family denotation

Define the concrete observed behavior of a finite family of paths by union:

```lean
def ExecPathFamilyDenotesObs
    (Relevant : ConcreteState Reg -> Prop)
    (observe : ConcreteState Reg -> Obs)
    (paths : Finset (List (Block Reg)))
    (s : ConcreteState Reg) (o : Obs) : Prop :=
  Relevant s /\
    \exists blocks \in paths, ExecBlockPathDenotesObs Relevant observe blocks s o
```

Define the extracted symbolic model of the same family by lower+union:

```lean
def lowerPathFamilySummaries
    (paths : Finset (List (Block Reg))) : Finset (Summary Reg) :=
  paths.biUnion fun blocks => lowerBlockPathSummaries blocks
```

Then define the observation-level summary denotation through `VexModelDenotesObs`.

### 2. First subsystem-level property

```lean
def ExtractiblePathFamilyModel
    (Relevant : ConcreteState Reg -> Prop)
    (observe : ConcreteState Reg -> Obs)
    (paths : Finset (List (Block Reg))) : Prop :=
  \forall s o,
    VexModelDenotesObs Relevant observe (lowerPathFamilySummaries paths) s o <->
      ExecPathFamilyDenotesObs Relevant observe paths s o
```

This is the first real subsystem theorem target.

### 3. Witnessed subsystem packaging

Once the family theorem exists, define a minimal subsystem witness:

```lean
structure SubsystemWitness (Reg : Type) where
  paths : Finset (List (Block Reg))
  entry : ConcreteState Reg -> Prop
  exit : ConcreteState Reg -> Prop
  valid : Prop
```

For the first pass, `valid` can stay abstract or be a conjunction of simple well-formedness requirements. The key point is that the theorem is parameterized by a witness rather than pretending arbitrary CFG closure is solved already.

Then:

```lean
def SubsystemExtractible
    (Relevant : ConcreteState Reg -> Prop)
    (observe : ConcreteState Reg -> Obs)
    (w : SubsystemWitness Reg) : Prop :=
  ExtractiblePathFamilyModel Relevant observe w.paths
```

This is deliberately modest: the first subsystem theorem is a packaging theorem over path-family extractibility.

## Theorems To Prove

### Batch A: Path-family denotation

1. Define `lowerPathFamilySummaries`
2. Define `ExecPathFamilyDenotesObs`
3. Define `ExtractiblePathFamilyModel`

Then prove the key bridge:

```lean
theorem lowerPathFamilySummaries_denotesObs_iff_execPathFamily
    (Relevant : ConcreteState Reg -> Prop)
    (observe : ConcreteState Reg -> Obs)
    (paths : Finset (List (Block Reg))) :
    ExtractiblePathFamilyModel Relevant observe paths
```

Proof idea:
- unfold `lowerPathFamilySummaries` as `Finset.biUnion`
- use `ModelDenotesObs.mono` / union reasoning from `ModelEq.lean`
- use `extractiblePathModel_of_lowering` path-by-path
- package both directions by membership in the path family

Likely helper lemmas:

```lean
theorem vexModelDenotesObs_biUnion_iff

theorem execPathFamilyDenotesObs_iff
```

### Batch B: Path-family composition

Once Batch A exists, prove the subsystem-level composition corollary:

```lean
theorem extractiblePathFamilyModel_union
    (h1 : ExtractiblePathFamilyModel Relevant observe paths1)
    (h2 : ExtractiblePathFamilyModel Relevant observe paths2) :
    ExtractiblePathFamilyModel Relevant observe (paths1 ∪ paths2)
```

This matters because real subsystems will likely be assembled from discovered path families.

### Batch C: Witnessed subsystem packaging

Define:
- `SubsystemWitness`
- `SubsystemExtractible`

Then prove:

```lean
theorem subsystemExtractible_of_pathWitness
    (Relevant : ConcreteState Reg -> Prop)
    (observe : ConcreteState Reg -> Obs)
    (w : SubsystemWitness Reg) :
    SubsystemExtractible Relevant observe w
```

This theorem is intentionally shallow: it packages the family theorem into a subsystem-shaped statement.

## Commit Plan

### Commit 1
`document subsystem extractibility plan`
- this doc only

### Commit 2
`add VEX path-family subsystem denotation`
- `lowerPathFamilySummaries`
- `ExecPathFamilyDenotesObs`
- `ExtractiblePathFamilyModel`
- any small helper defs

### Commit 3
`prove VEX path-family extractibility theorem`
- main theorem:
  - `lowerPathFamilySummaries_denotesObs_iff_execPathFamily`
- any helper lemmas needed for `Finset.biUnion` denotation equivalence

### Commit 4
`add VEX path-family subsystem composition lemma`
- union/composition corollary for path-family models

### Commit 5
`package witnessed subsystem extractibility`
- `SubsystemWitness`
- `SubsystemExtractible`
- packaging theorem

This is the likely minimum honest batch.

## Why This Order

This keeps the theorem tied to binary-descended objects throughout:
- blocks come from lifted binaries,
- paths are lists of lifted blocks,
- path families are finite unions of those,
- subsystems are witnessed by path families.

So the theorem is not about an invented abstract object detached from the binary. It is about a binary-descended semantic witness, just not the full arbitrary CFG closure yet.

## Review Questions

1. Is the finite path-family witness the right first subsystem object, or is there a better minimal witness that is still honest?
2. Should `SubsystemWitness.valid` stay abstract in the first pass, or should we immediately include entry/exit/path-validity fields explicitly?
3. Is `lowerPathFamilySummaries` as a `Finset.biUnion` the right first extracted model object, or should we package the family as a set-level denotation instead of a flattened `Finset`?
4. Is the composition corollary worth its own commit in this batch, or should it wait until after the witnessed packaging theorem?
