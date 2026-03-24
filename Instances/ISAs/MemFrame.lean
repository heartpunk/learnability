import Instances.ISAs.VexSyntax
import Mathlib.Tactic.IntervalCases
import Lean

/-!
# mem_frame tactic

Automates ByteMem read-after-write frame reasoning by walking the goal
expression tree and peeling non-overlapping writes from reads.
Uses ByteMem_read_write_ne with pointwise address distinctness.

Priority-ordered peeling: addresses without memory loads are processed first,
so inner reads normalize before outer reads that depend on them.
Skips patterns whose side conditions can't be discharged, so the tactic
peels everything it can and stops gracefully.

Region-aware discharger: when simple omega fails, unfolds hypothesis
definitions (e.g. StackSeparation, DataPtrInRegion) to expose bounds
on opaque UInt64 terms, then retries omega with those bounds.

This is the memo table step toward e-graph equality saturation.
-/

open Lean Meta Elab Tactic
open VexISA

/-- Check if expr matches `ByteMem.read lw (ByteMem.write sw M a v) b`. -/
private def matchReadOfWrite? (e : Expr) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  let (fn, args) := e.consumeMData.getAppFnArgs
  if fn == ``ByteMem.read && args.size == 3 then
    let lw := args[0]!; let mem := args[1]!; let b := args[2]!
    let (wfn, wargs) := mem.consumeMData.getAppFnArgs
    if wfn == ``ByteMem.write && wargs.size == 4 then
      some (lw, wargs[0]!, wargs[1]!, wargs[2]!, wargs[3]!, b)
    else none
  else none

/-- Check if expr contains any `ByteMem.read` subexpression. -/
private partial def containsRead (e : Expr) : Bool :=
  let ec := e.consumeMData
  let (fn, args) := ec.getAppFnArgs
  if fn == ``ByteMem.read && args.size == 3 then true
  else match ec with
    | .app f x => containsRead f || containsRead x
    | .letE _ t v b _ => containsRead t || containsRead v || containsRead b
    | .lam _ t b _ => containsRead t || containsRead b
    | .forallE _ t b _ => containsRead t || containsRead b
    | _ => false

/-- Score a read address by simplicity. Lower = simpler = process first.
    Addresses without memory loads (constants, register-relative) score 1.
    Addresses that contain memory loads (data pointers) score 2. -/
private def scoreReadAddr (b : Expr) : Nat :=
  if containsRead b then 2 else 1

/-- Collect all `ByteMem.read (ByteMem.write ...) addr` patterns in expression tree. -/
private partial def collectReadOfWrite (e : Expr) :
    Array (Expr × Expr × Expr × Expr × Expr × Expr) :=
  let ec := e.consumeMData
  let here := match matchReadOfWrite? ec with
    | some m => #[m]
    | none => #[]
  let children := match ec with
    | .app f x => collectReadOfWrite f ++ collectReadOfWrite x
    | _ => #[]
  here ++ children

/-- Walk expression tree, rewriting first matching read-of-write with a given proof.
    Matches on (lw, a, b) to identify the exact pattern. -/
private partial def rewriteFirst (e : Expr) (lw sw M a v b proof : Expr) :
    MetaM (Expr × Option Expr) := do
  let ec := e.consumeMData
  if let some (lw', _sw', _M', a', _v', b') := matchReadOfWrite? ec then
    if lw' == lw && b' == b && a' == a then
      return (← mkAppM ``ByteMem.read #[lw, M, b], some proof)
  match ec with
  | .app f x =>
    let (f', fp?) ← rewriteFirst f lw sw M a v b proof
    match fp? with
    | some fp => return (mkApp f' x, some (← mkCongrFun fp x))
    | none =>
      let (x', xp?) ← rewriteFirst x lw sw M a v b proof
      match xp? with
      | some xp => return (mkApp f x', some (← mkCongrArg f xp))
      | none => return (e, none)
  | _ => return (e, none)

/-- Try to peel one write from one read-of-write pattern using footprint disjointness.
    Three strategies in cascade:
    1. native_decide — fully concrete footprints
    2. Same-base cancellation — Disjoint_add_left + native_decide on offsets
    3. Stack-vs-ELF — eq_sub_of_add_eq + rw into StackSeparation + interval_cases -/
private def tryPeelOne (goal : MVarId) (goalType : Expr)
    (lw sw M a v b : Expr) : TacticM Bool := do
  -- Try three strategies to construct the frame proof
  let proof ← goal.withContext <| do
    -- Strategy 1: Footprint.Disjoint via native_decide (fully concrete)
    let s1 ← saveState
    try
      let writeFP ← mkAppM ``VexISA.Footprint.ofWidth #[a, sw]
      let readFP ← mkAppM ``VexISA.Footprint.ofWidth #[b, lw]
      let disjProp ← mkAppM ``VexISA.Footprint.Disjoint #[writeFP, readFP]
      let mvar ← mkFreshExprMVar (some disjProp)
      setGoals [mvar.mvarId!]
      evalTactic (← `(tactic| native_decide))
      mkAppM ``VexISA.ByteMem_read_write_of_disjoint #[lw, sw, M, a, v, b, mvar]
    catch _ =>
      s1.restore
      -- Strategy 2: Footprint.Disjoint via same-base cancellation
      let s2 ← saveState
      try
        let writeFP ← mkAppM ``VexISA.Footprint.ofWidth #[a, sw]
        let readFP ← mkAppM ``VexISA.Footprint.ofWidth #[b, lw]
        let disjProp ← mkAppM ``VexISA.Footprint.Disjoint #[writeFP, readFP]
        let mvar ← mkFreshExprMVar (some disjProp)
        setGoals [mvar.mvarId!]
        evalTactic (← `(tactic| (
          apply VexISA.Footprint.Disjoint_add_left
          native_decide)))
        mkAppM ``VexISA.ByteMem_read_write_of_disjoint #[lw, sw, M, a, v, b, mvar]
      catch _ =>
        s2.restore
        -- Strategy 3: ByteMem_frame_of_separate via Iris separation
        -- Construct the frame equality directly. The proof context must
        -- have ByteHeap witnesses with valid composition (from Iris ∗).
        let eqType ← mkAppM ``Eq #[
          ← mkAppM ``VexISA.ByteMem.read #[lw, ← mkAppM ``VexISA.ByteMem.write #[sw, M, a, v], b],
          ← mkAppM ``VexISA.ByteMem.read #[lw, M, b]]
        let mvar ← mkFreshExprMVar (some eqType)
        setGoals [mvar.mvarId!]
        evalTactic (← `(tactic|
          exact VexISA.ByteMem_frame_of_separate _ _ _ _ _ _ _ _ (by assumption) (by assumption) (by assumption)))
        return mvar
  -- Rewrite the goal
  let (newType, eqProof?) ← goal.withContext (rewriteFirst goalType lw sw M a v b proof)
  match eqProof? with
  | none => return false
  | some eqProof =>
    let newGoal ← goal.replaceTargetEq newType eqProof
    replaceMainGoal [newGoal]
    return true

/-- Reduce closed (no free variables) UInt64 subexpressions to literals.
    Walks the expression tree, finds UInt64-typed subexpressions with no fvars,
    and replaces them with their kernel-evaluated form. -/
private partial def reduceClosedUInt64 (e : Expr) : MetaM Expr := do
  let ec := e.consumeMData
  -- If closed, check if it's UInt64-typed and reducible
  if !ec.hasFVar && !ec.hasMVar then
    -- Only try reduction on applications (not already-reduced literals/consts)
    if ec.isApp then
      let ty ← try inferType ec catch _ => return e
      if ty.isConstOf ``UInt64 then
        let r ← withTransparency .all <| whnf ec
        if r != ec then
          -- whnf produces raw struct { toBitVec := N#64 }.
          -- Extract the Nat value and reconstruct as a proper OfNat literal
          -- so simp [toNat_ofNat] can match.
          let natVal ← try
            let nExpr ← withTransparency .all <| reduce (← mkAppM ``UInt64.toNat #[r])
            pure nExpr.rawNatLit?
          catch _ => pure none
          match natVal with
          | some n => return ← mkNumeral (mkConst ``UInt64) n
          | none => return r
  -- Recurse into applications
  match ec with
  | .app f x =>
    let f' ← reduceClosedUInt64 f
    let x' ← reduceClosedUInt64 x
    if f' == f && x' == x then return e
    return mkApp f' x'
  | _ => return e

/-- Canonicalize UInt64 address arithmetic in the goal.
    Step 1: Right-associate chained add/sub so constants group together.
    Step 2: Reduce closed UInt64 subexpressions via kernel evaluation.
    Result: `rbp + 8 + 8 - 72` becomes `rbp + 18446744073709551560`. -/
private def canonicalizeAddresses : TacticM Unit := do
  -- Step 1: Right-associate chained add/sub
  let _ ← tryTactic do
    evalTactic (← `(tactic|
      simp (config := { failIfUnchanged := false }) only [
        UInt64.add_assoc, UInt64.add_sub, UInt64.sub_add] at *))
  -- Step 2: Evaluate closed UInt64 constants via MetaM reduction
  let goal ← getMainGoal
  let goalType ← goal.getType
  let newType ← goal.withContext <| reduceClosedUInt64 goalType
  if newType != goalType then
    let newGoal ← goal.replaceTargetDefEq newType
    replaceMainGoal [newGoal]

/-- The `mem_frame` tactic. Peels non-overlapping writes from reads,
    processing simpler addresses first so inner reads normalize before
    outer reads that depend on them. Skips patterns it can't discharge. -/
elab "mem_frame" : tactic => do
  -- Phase 0: Canonicalize UInt64 address arithmetic
  canonicalizeAddresses
  let mut fuel := 50
  let mut progress := false
  while fuel > 0 do
    fuel := fuel - 1
    let goal ← getMainGoal
    let goalType ← goal.getType
    let candidates := collectReadOfWrite goalType
    if candidates.isEmpty then break
    let scored := candidates.map fun m => (scoreReadAddr m.2.2.2.2.2, m)
    let sorted := scored.qsort fun a b => a.1 < b.1
    let mut peeled := false
    for idx in [:sorted.size] do
      if peeled then break
      let item := sorted[idx]!
      let lw := item.2.1
      let sw := item.2.2.1
      let M := item.2.2.2.1
      let a := item.2.2.2.2.1
      let v := item.2.2.2.2.2.1
      let b := item.2.2.2.2.2.2
      let saved ← saveState
      try
        let ok ← tryPeelOne goal goalType lw sw M a v b
        if ok then
          peeled := true
          progress := true
        else
          saved.restore
      catch _ =>
        saved.restore
    if !peeled then break
  unless progress do
    throwError "mem_frame: no ByteMem.read (ByteMem.write ...) patterns could be simplified"
