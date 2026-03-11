# Proof Compression Plan

## Overview

Create `Instances/ISAs/VexProofCompression.lean` containing **8 new lemmas** that abstract
repeated proof patterns across the ISA files. Three commits: general abstractions, Phase 3 Target 1
(hStep), Phase 3 Target 2 (PC-signature independence).

---

## Background: What Was Surveyed

The top repeated patterns in `Instances/ISAs/` and `SymExec/`:

| Pattern | Occurrences | Files |
|---|---|---|
| `linearStmtBridge.sound` stepping | 4× (L119-121, L235-237 of VexLoweringCorrectness; L93-95 of VexCompTree; L120 of VexLoweringCorrectness) | VexLoweringCorrectness, VexCompTree |
| `bodyEffect_spec` for `assign (lowerBlockSub b)` | 2× | Tier6LoopWitness, Tier7BodyRefinement |
| `simpa [..] using` | 27× | VexLoweringCorrectness, VexCompTree |
| Induction `nil/cons` + nested `cases stmt` | 4 major theorems | VexLoweringCorrectness |
| `refine ⟨?_, ?_⟩` constructor | 18× | VexWitness |

The first two have a clean lemma extraction. The `simpa` and `refine` patterns are more
situational — they appear with different simp sets each time — so we focus on clean structural
abstractions rather than trying to package them.

---

## New File: `Instances/ISAs/VexProofCompression.lean`

### Imports
```lean
import Instances.ISAs.VexCompTree   -- treeBehavior_blockToCompTree, blockToCompTree,
                                    --   lowerBlockSub_sound
import Instances.ISAs.VexWitness    -- VexLoopSummary, pcSignatureWith (via
                                    --   SymExec.Refinement → SymExec.Quotient)
```

`VexWitness` already transitively provides `pcSignatureWith` (through
`SymExec.Refinement → SymExec.Quotient`), `VexLoopSummary`, `vexSummaryISA`,
`PartialSummaryMatches`, `evalSymExpr`, `evalSymPC`, etc.

### Namespace: `VexISA`

---

## Commit 1 — General Abstractions (Lemmas 1–2)

### Lemma 1: `partialSummaryMatches_linearStmt_step`

**What it abstracts:** This 3-line block repeated 4× across VexLoweringCorrectness and VexCompTree:
```lean
have hMatchLinear : LowerStateMatches input concrete (ps.sub, ps.temps) := hMatch
have hStep := (linearStmtBridge stmt).sound input concrete (ps.sub, ps.temps) hMatchLinear
simpa [ps', lowered, LowerStateMatches, PartialSummaryMatches] using hStep
```

**Signature:**
```lean
theorem partialSummaryMatches_linearStmt_step
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (stmt : LinearStmt Reg)
    (concrete : ConcreteState Reg × TempEnv) (ps : PartialSummary Reg)
    (hMatch : PartialSummaryMatches input concrete ps) :
    let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
    PartialSummaryMatches input
      (execLinearStmt concrete stmt)
      { ps with sub := lowered.1, temps := lowered.2 }
```

**Proof sketch:**
```lean
  have hStep := (linearStmtBridge stmt).sound input concrete (ps.sub, ps.temps) hMatch
  simpa [execLinearStmt, lowerLinearStmt, LowerStateMatches, PartialSummaryMatches] using hStep
```

**Type justification:** `PartialSummaryMatches` and `LowerStateMatches` are both abbreviations
for `BridgeInvariant input concrete sub temps`, so the return types agree definitionally once
`execLinearStmt` and `lowerLinearStmt` are unfolded (both are `@[inline]` wrappers over
`(linearStmtBridge stmt).exec/.lower`). The `simpa` handles the unfolding.

---

### Lemma 2: `bodyEffect_spec_assign_lowerBlockSub`

**What it abstracts:** The `bodyEffect_spec` proof for any loop whose body is
`CompTree.assign (lowerBlockSub block)`. Used verbatim in Tier6LoopWitness and Tier7BodyRefinement:
```lean
bodyEffect_spec := by
  intro s s'
  simpa [CompTree.treeBehavior, assignBehavior] using
    (show (s' = applySymSub (lowerBlockSub block) s) ↔ s' = execBlock block s by
      rw [lowerBlockSub_sound block s])
```

**Signature:**
```lean
theorem bodyEffect_spec_assign_lowerBlockSub
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) :
    ∀ s s',
      CompTree.treeBehavior (vexSummaryISA Reg)
        (CompTree.assign (lowerBlockSub block)) s s' ↔
        s' = execBlock block s
```

**Proof sketch:**
```lean
  intro s s'
  simp only [CompTree.treeBehavior, assignBehavior, vexSummaryISA]
  -- goal: s' = applySymSub (lowerBlockSub block) s ↔ s' = execBlock block s
  constructor
  · intro h; rwa [lowerBlockSub_sound] at h
  · intro h; rwa [← lowerBlockSub_sound] at h
```

**Key fact:** `assignBehavior isa σ s s' := s' = isa.eval_sub σ s` (from `Core/Composition.lean`).
For `vexSummaryISA Reg`, `eval_sub = applySymSub`. And
`lowerBlockSub_sound block s : applySymSub (lowerBlockSub block) s = execBlock block s`.

---

## Commit 2 — Phase 3 Target 1: hStep Derivation (Lemmas 3–4)

**Motivation:** `dispatch_bodyPathStepRealizable` (VexDispatchLoop.lean) takes as a black-box
hypothesis:
```lean
hStep : ∀ s, ∃ b ∈ allBlocks, loop.bodyEffect s ∈ execBlockSuccs b s
```
When a loop's body is literally `blockToCompTree b`, this hypothesis is trivial to prove from
`bodyEffect_spec` + `treeBehavior_blockToCompTree`, but the chain is non-obvious and requires
knowing both theorems simultaneously.

### Lemma 3: `bodyEffect_mem_execBlockSuccs`

**Signature:**
```lean
theorem bodyEffect_mem_execBlockSuccs
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (loop : VexLoopSummary Reg) (b : Block Reg)
    (hBody : loop.body = blockToCompTree b)
    (s : ConcreteState Reg) :
    loop.bodyEffect s ∈ execBlockSuccs b s
```

**Proof:**
```lean
  rw [← treeBehavior_blockToCompTree b s (loop.bodyEffect s)]
  rw [← hBody]
  exact (loop.bodyEffect_spec s (loop.bodyEffect s)).mpr rfl
```

**Chain:**
1. `treeBehavior_blockToCompTree b s s' : treeBehavior ... (blockToCompTree b) s s' ↔ s' ∈ execBlockSuccs b s`
2. After `rw [← ...]`, goal becomes `treeBehavior ... (blockToCompTree b) s (loop.bodyEffect s)`
3. After `rw [← hBody]`, goal becomes `treeBehavior ... loop.body s (loop.bodyEffect s)`
4. `loop.bodyEffect_spec s (loop.bodyEffect s) : treeBehavior ... loop.body s s' ↔ s' = loop.bodyEffect s`
5. `.mpr rfl` closes it since `loop.bodyEffect s = loop.bodyEffect s`.

### Lemma 4: `hStep_of_singleBlock`

**Signature:**
```lean
theorem hStep_of_singleBlock
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (loop : VexLoopSummary Reg) (b : Block Reg)
    (hBody : loop.body = blockToCompTree b) :
    ∀ s, ∃ b' ∈ ({b} : Finset (Block Reg)), loop.bodyEffect s ∈ execBlockSuccs b' s
```

**Proof:**
```lean
  intro s
  exact ⟨b, Finset.mem_singleton_self b, bodyEffect_mem_execBlockSuccs loop b hBody s⟩
```

**Usage:** Callers can now write:
```lean
have hStep := hStep_of_singleBlock loop b hBody
-- then immediately:
exact dispatch_bodyPathStepRealizable loop ({b} : Finset _) closure hStep
```
Instead of manually threading `bodyEffect_spec` + `treeBehavior_blockToCompTree`.

---

## Commit 3 — Phase 3 Target 2: PC-Signature Independence (Lemmas 5–8)

**Motivation:** For dispatch-loop convergence on mutually-recursive CFG parsers, the closure
of SymPCs need not mention the stack pointer `rsp` or memory. Two states at different call
depths but with the same `rip` and input-register values should therefore have identical
PC-signatures. This lemma makes that precise and enables reuse across any similarly-structured
closure.

### Definitions 5a–5b: `SymExpr.RegOnly`, `SymPC.RegOnly`

```lean
/-- A SymExpr mentions only registers in `allowed` and contains no memory reads. -/
def SymExpr.RegOnly {Reg : Type} (allowed : Finset Reg) : SymExpr Reg → Prop
  | .const _      => True
  | .reg r        => r ∈ allowed
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e => SymExpr.RegOnly allowed e
  | .sub32 l r | .shl32 l r | .add64 l r | .sub64 l r
  | .xor64 l r | .and64 l r | .or64 l r | .shl64 l r | .shr64 l r =>
      SymExpr.RegOnly allowed l ∧ SymExpr.RegOnly allowed r
  | .load _ _ _   => False     -- no memory reads allowed

/-- A SymPC is register-only when all embedded SymExprs are. -/
def SymPC.RegOnly {Reg : Type} (allowed : Finset Reg) : SymPC Reg → Prop
  | .true     => True
  | .eq l r | .lt l r | .le l r =>
      SymExpr.RegOnly allowed l ∧ SymExpr.RegOnly allowed r
  | .and φ ψ  => SymPC.RegOnly allowed φ ∧ SymPC.RegOnly allowed ψ
  | .not φ    => SymPC.RegOnly allowed φ
```

**Decidability note:** `SymExpr.RegOnly` can be made `Decidable` (it's a syntactic check) —
useful for `native_decide` in concrete examples. Not needed for the abstract lemmas.

### Lemma 6: `evalSymExpr_congr_of_regOnly`

```lean
theorem evalSymExpr_congr_of_regOnly
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {allowed : Finset Reg} {e : SymExpr Reg}
    (he : SymExpr.RegOnly allowed e)
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    evalSymExpr s₁ e = evalSymExpr s₂ e
```

**Proof strategy:** Structural induction (`cases e with`) following the same pattern as
`substSymExpr_id` and `evalSymExpr_subst` in `VexSummary.lean`. Those use `mutual` blocks;
here we don't need one because the `.load` case is immediately closed by `he.elim`
(since `SymExpr.RegOnly allowed (.load _ _ _) = False`).

```lean
  cases e with
  | const _     => rfl
  | reg r       => exact hRegs r he
  | low32 e     => simp only [evalSymExpr]; rw [evalSymExpr_congr_of_regOnly he hRegs]
  | uext32 e    => simp only [evalSymExpr]; rw [evalSymExpr_congr_of_regOnly he hRegs]
  | sext8to32 e => simp only [evalSymExpr]; rw [evalSymExpr_congr_of_regOnly he hRegs]
  | sext32to64 e => simp only [evalSymExpr]; rw [evalSymExpr_congr_of_regOnly he hRegs]
  | sub32 l r   => rcases he with ⟨hl, hr⟩
                   simp only [evalSymExpr]
                   rw [evalSymExpr_congr_of_regOnly hl hRegs,
                       evalSymExpr_congr_of_regOnly hr hRegs]
  -- ... same for shl32, add64, sub64, xor64, and64, or64, shl64, shr64
  | load _ _ _  => simp [SymExpr.RegOnly] at he   -- derives False, closes goal
```

**Lean 4 implementation note:** Because `SymExpr` is mutually recursive with `SymMem`, self-
referential `cases` proofs need either a `mutual` block (like `substSymExpr_id`) or a
`termination_by` annotation. We will write this inside a `mutual` block with a trivial companion
`evalSymMem_congr_aux` (for the `SymMem` component of `.load`'s motive). The companion need not
be exported since the `.load` case is vacuous (`he.elim`). **Fallback:** if the mutual block causes
elaboration issues, switch to `Nat`-sized well-founded recursion using
`termination_by e.sizeof`.

### Lemma 7: `evalSymPC_congr_of_regOnly`

```lean
theorem evalSymPC_congr_of_regOnly
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {allowed : Finset Reg} {φ : SymPC Reg}
    (hφ : SymPC.RegOnly allowed φ)
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    evalSymPC s₁ φ = evalSymPC s₂ φ
```

**Proof:** `SymPC` is NOT in the `mutual` block with `SymMem`, so plain `cases φ with` works.
```lean
  cases φ with
  | true     => rfl
  | eq l r   => rcases hφ with ⟨hl, hr⟩
                simp only [evalSymPC,
                  evalSymExpr_congr_of_regOnly hl hRegs,
                  evalSymExpr_congr_of_regOnly hr hRegs]
  | lt l r   => -- same as eq
  | le l r   => -- same as eq
  | and φ ψ  => rcases hφ with ⟨hφ', hψ'⟩
                simp only [evalSymPC,
                  evalSymPC_congr_of_regOnly hφ' hRegs,
                  evalSymPC_congr_of_regOnly hψ' hRegs]
  | not φ    => simp only [evalSymPC, evalSymPC_congr_of_regOnly hφ hRegs]
```

Note: `SymPC` has no `mutual` recursion issue, so self-referential `cases` with `simp [evalSymPC_congr_of_regOnly]` should work directly (as in the `substSymPC_compose` proof in `VexSummaryISA.lean`).

### Lemma 8: `pcSignatureWith_congr_of_regOnly`

```lean
/-- **PC-signature independence.**
    If every SymPC in `closure` is register-only w.r.t. `allowed`, and `s₁` and `s₂`
    agree on all registers in `allowed`, then their PC-signatures are equal.
    In particular, registers outside `allowed` (e.g. `rsp`, stack frame, memory)
    do not affect the signature. -/
theorem pcSignatureWith_congr_of_regOnly
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (closure : Finset (SymPC Reg))
    (allowed : Finset Reg)
    (hClosure : ∀ φ ∈ closure, SymPC.RegOnly allowed φ)
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    pcSignatureWith (vexSummaryISA Reg) closure s₁ =
      pcSignatureWith (vexSummaryISA Reg) closure s₂
```

**Proof:**
```lean
  unfold pcSignatureWith
  apply Finset.filter_congr
  intro φ hφ
  simp only [vexSummaryISA, satisfiesSymPC]
  -- goal: evalSymPC s₁ φ = true ↔ evalSymPC s₂ φ = true
  rw [evalSymPC_congr_of_regOnly (hClosure φ hφ) hRegs]
```

`Finset.filter_congr` has signature:
```lean
theorem Finset.filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    {s : Finset α} (h : ∀ x ∈ s, p x ↔ q x) : s.filter p = s.filter q
```
After `rw [evalSymPC_congr_of_regOnly ...]`, the LHS and RHS of the iff become identical, closed by `Iff.rfl`.

---

## Changes to `Instances.lean`

Add three import lines after `import Instances.ISAs.VexSummaryISA` (around line 94):
```lean
import Instances.ISAs.VexCompTree
import Instances.ISAs.VexDispatchLoop
import Instances.ISAs.VexProofCompression
```

(VexDispatchLoop is currently not imported either; adding it makes the dispatch loop theorem
publicly visible from the `Instances` library target.)

---

## Commit Plan

**Invariant:** Every commit introduces exactly one new lemma or tactic, plus all refactoring of
existing call sites. Net codebase reduction is required. Commits that add new infrastructure with
no existing call sites must carry an explicit **super compelling reason** (SCR) — a concrete
justification for why the new lemma is prerequisite infrastructure rather than optional polish.

---

### Commit 1: `partialSummaryMatches_linearStmt_step` — NET NEGATIVE ✓

**New code:**
- `Instances/ISAs/VexProofCompression.lean` — created; imports `VexWitness` only; lemma 1 + header
- `Instances.lean` — add `import Instances.ISAs.VexProofCompression`

**Refactored (existing call sites removed):**
- `Instances/ISAs/VexLoweringCorrectness.lean` — the 3-line stepping block repeated at ~L119–121, ~L235–237, and 2+ additional sites
- `Instances/ISAs/VexCompTree.lean` — the 3-line stepping block at ~L93–95

**Net:** ~15 lines added, ~25+ lines removed → **net negative**

Background review: 2 subagents (build+proofs, integration)

---

### Commit 2: `bodyEffect_spec_assign_lowerBlockSub` — NET NEGATIVE ✓

**New code:**
- `Instances/ISAs/VexProofCompression.lean` — add lemma 2 (~8 lines)

**Refactored:**
- `Instances/Examples/Tier6LoopWitness.lean` — replace 4-line `bodyEffect_spec` block with 1-line call
- `Instances/Examples/Tier7BodyRefinement.lean` — same

**Net:** ~8 lines added, ~12 lines removed → **net negative**

Background review: 2 subagents

---

### Commit 3: `hStep_of_singleBlock` — NET POSITIVE (SCR)

**New code:**
- `Instances/ISAs/VexProofCompression.lean` — add `import Instances.ISAs.VexCompTree`; add private `bodyEffect_mem_execBlockSuccs` helper + public `hStep_of_singleBlock` (~15 lines total)
- `Instances.lean` — add `import Instances.ISAs.VexCompTree` and `import Instances.ISAs.VexDispatchLoop`

**No existing call sites to refactor.** Net positive (~18 lines added).

**SCR:** `dispatch_bodyPathStepRealizable` — described in VexDispatchLoop.lean as "the ONLY new
proof needed for the full interprocedural grammar extraction pipeline" — takes `hStep` as a
black-box hypothesis. Without this lemma, every single-block-body dispatch loop caller must
manually chain `loop.bodyEffect_spec` (SymExec.CircularCoinduction) with
`treeBehavior_blockToCompTree` (Instances.ISAs.VexCompTree) across a two-file import boundary
and reason about Finset membership — three steps that cannot be packaged without this lemma.
`hStep_of_singleBlock` IS the bridge. The alternative is copy-pasting those three steps into every
future dispatch loop proof.

Background review: 2 subagents

---

### Commit 4: `evalSymExpr_congr_of_regOnly` — NET POSITIVE (SCR)

**New code:**
- `Instances/ISAs/VexProofCompression.lean` — add `SymExpr.RegOnly` definition, `SymPC.RegOnly`
  definition, and `evalSymExpr_congr_of_regOnly` (with `private` mutual companion for `SymMem`)
  (~40 lines total)

The `SymExpr.RegOnly` / `SymPC.RegOnly` definitions have no value without the first lemma that
uses them; they are bundled here rather than in a standalone commit.

**No existing call sites.** Net positive.

**SCR:** `pcSignatureWith_congr_of_regOnly` (commit 6) — the terminal theorem for Phase 3 Target 2
— requires showing `evalSymPC s₁ φ = evalSymPC s₂ φ`, which requires showing
`evalSymExpr s₁ e = evalSymExpr s₂ e` for sub-expressions. There is no existing proof of this
congruence property anywhere in the codebase. `evalSymExpr_congr_of_regOnly` formalizes the
necessary structural invariant (SymExpr depends only on named registers, not memory) and is
the mandatory foundation for the two subsequent lemmas.

Background review: 2 subagents

---

### Commit 5: `evalSymPC_congr_of_regOnly` — NET POSITIVE (SCR)

**New code:**
- `Instances/ISAs/VexProofCompression.lean` — add `evalSymPC_congr_of_regOnly` (~15 lines)

**No existing call sites.** Net positive.

**SCR:** Required by `pcSignatureWith_congr_of_regOnly` (commit 6), where the proof calls
`rw [evalSymPC_congr_of_regOnly ...]` inside `Finset.filter_congr`. Inlining the proof of
`evalSymPC` congruence into commit 6 would make that commit add two distinct logical units
(SymPC-level congruence + Finset filter equality), violating the one-lemma-per-commit rule.
Separating it here keeps each commit's logical content atomic.

Background review: 2 subagents

---

### Commit 6: `pcSignatureWith_congr_of_regOnly` — NET POSITIVE (SCR)

**New code:**
- `Instances/ISAs/VexProofCompression.lean` — add `pcSignatureWith_congr_of_regOnly` (~10 lines)

**No existing call sites.** Net positive.

**SCR:** This is Phase 3 Target 2. It formalizes stack-depth independence of PC signatures: two
states at different call depths but with the same input-register values (no rsp/memory terms in
closure) produce identical PC signatures, so `BranchClassesStable` holds with
`K = 2^|closure|` regardless of recursion depth. Without this lemma, every convergence proof
for a mutually-recursive dispatch loop must reprove this property ad hoc. It is the missing
formalization of the key insight stated informally in `VexDispatchLoop.lean` line 26: "Two states
at different call depths reading the same character have identical PC signatures." That claim
currently has no proof in the codebase.

Background review: 2 subagents

---

## Risk Register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `induction`/`cases` fails on mutual `SymExpr`/`SymMem` for lemma 6 | Medium | Wrap in `mutual` block with trivial `evalSymMem_congr_aux` companion, or use `termination_by e.sizeof` |
| `simpa` in lemma 1 needs extra simp lemmas | Low | Start with `simpa [execLinearStmt, lowerLinearStmt, LowerStateMatches, PartialSummaryMatches]` matching existing call sites exactly |
| `Finset.filter_congr` API differs in this Mathlib version | Low | Check with `#check @Finset.filter_congr` at build time; fallback is `ext φ; simp [pcSignatureWith, Finset.mem_filter, ...]` |
| `VexCompTree` not yet in `Instances` build target | None | Confirmed: it's not in `Instances.lean` today, will be added |
| `SymExpr.RegOnly` definition not `Decidable` | None | Not needed for the theorems; can add later if native_decide tests are wanted |

---

## Concrete AMD64 Instantiation (Documentation Only, Not a New Lemma)

For reference, the typical "no rsp/memory" closure in AMD64 dispatch loops would use:
```lean
allowed := ({.rax, .rcx, .rdx, .rsi, .rbp, .rdi, .rip,
              .cc_op, .cc_dep1, .cc_dep2, .cc_ndep} : Finset Amd64Reg)
-- i.e., Finset.univ \ {.rsp}
```
and callers prove `SymPC.RegOnly allowed φ` for each `φ ∈ closure` by `decide` (since
`Amd64Reg` is a `Fintype` and `SymPC.RegOnly` is decidable once we add the instance).

---

## Open Questions for Approval

1. **Lemma 6 mutual block:** Acceptable to have a `private` companion `evalSymMem_congr_aux`
   that is never exported but needed for the structural recursion? (The alternative is a
   `termination_by e.sizeof` annotation on the single theorem.)
