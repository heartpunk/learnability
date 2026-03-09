# Tier Redesign Plan

The current tier ladder over-tests local block facts and under-tests composition. The next
ladder should be organized around the missing criteria, not around the historical order of
examples.

## Collapse / Keep

Phase 1 should collapse the old block-local examples into a small basis:
- one straight-line representative
- one branching representative

That is enough to retain smoke coverage for lowering, `SemClosed`, and the single-block
`CrossBisimulation` pipeline. The real new value starts at composition.

## New Phase Progression

### Phase 1: Block-local representatives
Targets:
- single-path straight-line block
- single-block branching block

Criteria exercised:
- baseline lowering / branch model / `SemClosed`
- no new criteria beyond local sanity

### Phase 2: Two-block composition
Targets:
- `C1` multi-block path composition
- `C3` `SemClosed` for composed summaries
- `C4` cross-block state dependency

### Phase 3: Combinatorial path branching
Targets:
- `C2` genuine different block sequences
- `C6` multiple live classes / different states choose different paths

### Phase 4: Real loop with K >= 1
Targets:
- `C5` body actually executes
- `C7` concrete discharge of `BranchClassesStable`

### Phase 5: Capstone
Targets:
- `C8` compression theorem chain
- `C9` multi-path witness completeness with at least 3 genuine paths

## Phase 2: Concrete block definitions

Use existing opcodes only. Introduce a dedicated tiny register set for the composition tier:

```lean
inductive ComposeReg where
  | r0   -- input/data register
  | r1   -- instruction pointer register
  | r2   -- cross-block scratch/state
  deriving DecidableEq, Repr
```

Use `r1` as `ip_reg` in both blocks.

### Block A

Purpose:
- writes state that block B will branch on
- forces summary composition to thread substitutions across blocks

Definition:

```lean
def blockA : Block ComposeReg :=
  { stmts :=
      [Stmt.put .r2 (Expr.add64 (Expr.get .r0) (Expr.const 1))]
    ip_reg := .r1
    next := 1 }
```

Effect:
- `r2 := r0 + 1`
- `r1 := 1` by block fallthrough

### Block B

Purpose:
- branches on the value written by block A
- makes the composed path condition strictly harder than the single-block one

Definition:

```lean
def blockB : Block ComposeReg :=
  { stmts :=
      [Stmt.branch
        (BranchStmt.exit
          (Cond.eq64 (Expr.get .r2) (Expr.const 0))
          0x1000)]
    ip_reg := .r1
    next := 2 }
```

Effect:
- taken path: if `r2 = 0`, set `r1 := 0x1000`
- fallthrough path: otherwise set `r1 := 2`

### Why this is the right Phase 2 pair

This pair exercises the intended criteria cleanly:

#### C1: Multi-block path composition
The path `[blockA, blockB]` is the first real composed path. The result is not a union of two
independent single-block models; block B consumes block A's output.

#### C3: `SemClosed` for composed summaries
The branch PC in block B is initially:

```lean
r2 == 0
```

After composing through block A, the taken-path PC becomes:

```lean
(r0 + 1) == 0
```

That is the first nontrivial `pc_lift` through a composed substitution. This is the exact
"strictly harder than single-block" case we want.

#### C4: Cross-block state dependency
Block A writes `r2`. Block B branches on `r2`. The composed proof must show that the state
written in A is the state tested in B.

## Expected path family shape

For Phase 2, the natural path family is still a single block sequence:

```lean
def pathAB : List (Block ComposeReg) := [blockA, blockB]
```

The branching happens inside `blockB`, so this phase does **not** yet exercise `C2`. That is
intentional: Phase 2 is about composition, not combinatorial path families.

## Expected composed summaries

The lowered composed path should have two summaries:
- taken summary with PC equivalent to `(r0 + 1) == 0`
- fallthrough summary with PC equivalent to `not ((r0 + 1) == 0)`

This gives the smallest honest target for:
- explicit `Summary.compose`
- composed-path `SemClosed`
- composed `CrossBisimulation`

## Non-goals for Phase 2

Do **not** add:
- new opcodes
- loops
- multi-path witnesses
- CFG closure / fetched-program machinery beyond what is needed for the two-block path

Phase 2 should stay focused on the first genuinely nontrivial composition fact.
