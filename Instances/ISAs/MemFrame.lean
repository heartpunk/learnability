import Instances.ISAs.VexSyntax
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

/-- Try to peel one write from one read-of-write pattern. Returns true on success. -/
private def tryPeelOne (goal : MVarId) (goalType : Expr)
    (lw sw M a v b : Expr) : TacticM Bool := do
  let hpType ← goal.withContext <| do
    let swBC ← mkAppM ``VexISA.Width.byteCount #[sw]
    let lwBC ← mkAppM ``VexISA.Width.byteCount #[lw]
    withLocalDeclD `i (mkConst ``Nat) fun i =>
    withLocalDeclD `j (mkConst ``Nat) fun j => do
      let hi ← mkAppM ``LT.lt #[i, swBC]
      let hj ← mkAppM ``LT.lt #[j, lwBC]
      let oi ← mkAppM ``UInt64.ofNat #[i]
      let oj ← mkAppM ``UInt64.ofNat #[j]
      let ai ← mkAppM ``HAdd.hAdd #[a, oi]
      let bj ← mkAppM ``HAdd.hAdd #[b, oj]
      let neq ← mkAppM ``Ne #[ai, bj]
      let body ← mkArrow hj neq
      let body ← mkArrow hi body
      let body ← mkForallFVars #[j] body
      mkForallFVars #[i] body
  -- Create mvar with goal's local context so discharger sees hypotheses
  let hp ← goal.withContext <| mkFreshExprMVar (some hpType)
  let proof ← goal.withContext <|
    mkAppM ``VexISA.ByteMem_read_write_ne #[lw, sw, M, a, v, b, hp]
  -- Discharge hp
  let mvars ← getMVars proof
  for mvar in mvars do
    if ← mvar.isAssigned then continue
    setGoals [mvar]
    let saved ← saveState
    -- Fast path: simp + omega (handles constant and stack-relative addresses)
    try
      evalTactic (← `(tactic| (
        intro i j hi hj
        simp only [Width.byteCount] at hi hj
        (intro heq; have heq_nat := congrArg UInt64.toNat heq
         simp only [UInt64.toNat_add, UInt64.size, UInt64.toBitVec_toNat] at *
         omega))))
    catch _ =>
      -- Slow path: unfold hypothesis definitions for region-based reasoning.
      -- Definitions like StackSeparation and DataPtrInRegion are opaque to
      -- omega. Unfolding them exposes the bounds that omega needs.
      saved.restore
      setGoals [mvar]
      evalTactic (← `(tactic| (
        intro i j hi hj
        simp only [Width.byteCount] at hi hj
        intro heq; have heq_nat := congrArg UInt64.toNat heq)))
      let g ← getMainGoal
      let mut g' := g
      let lctx := (← g'.getDecl).lctx
      for decl in lctx do
        if decl.isAuxDecl then continue
        match ← unfoldDefinition? decl.type with
        | some unfolded =>
          if unfolded == decl.type then continue
          try g' ← g'.changeLocalDecl decl.fvarId unfolded
          catch _ => continue
        | none => continue
      replaceMainGoal [g']
      evalTactic (← `(tactic| (
        simp only [UInt64.toNat_add, UInt64.size, UInt64.toBitVec_toNat] at *
        omega)))
  -- Rewrite the goal
  let (newType, eqProof?) ← goal.withContext (rewriteFirst goalType lw sw M a v b proof)
  match eqProof? with
  | none => return false
  | some eqProof =>
    let newGoal ← goal.replaceTargetEq newType eqProof
    replaceMainGoal [newGoal]
    return true

/-- The `mem_frame` tactic. Peels non-overlapping writes from reads,
    processing simpler addresses first so inner reads normalize before
    outer reads that depend on them. Skips patterns it can't discharge. -/
elab "mem_frame" : tactic => do
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
