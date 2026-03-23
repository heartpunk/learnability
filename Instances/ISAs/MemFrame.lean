import Instances.ISAs.VexSyntax
import Lean

/-!
# mem_frame tactic

Automates ByteMem read-after-write frame reasoning by walking the goal
expression tree and peeling non-overlapping writes from reads.
Uses ByteMem_read_write_ne with pointwise address distinctness.

Priority-ordered peeling: addresses without memory loads are processed first,
so inner reads normalize before outer reads that depend on them.
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

/-- Find the read-of-write with the simplest address (priority-ordered peeling).
    Returns the pattern whose read address has fewest nested memory loads. -/
private def findSimplestReadOfWrite (e : Expr) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  let all := collectReadOfWrite e
  let scored := all.map fun m => (scoreReadAddr m.2.2.2.2.2, m)
  let sorted := scored.qsort fun a b => a.1 < b.1
  sorted[0]?.map (·.2)

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

/-- The `mem_frame` tactic. Peels non-overlapping writes from reads,
    processing simpler addresses first so inner reads normalize before
    outer reads that depend on them. -/
elab "mem_frame" : tactic => do
  let mut fuel := 50
  let mut progress := false
  while fuel > 0 do
    fuel := fuel - 1
    let goal ← getMainGoal
    let goalType ← goal.getType
    let some (lw, sw, M, a, v, b) := findSimplestReadOfWrite goalType
      | break
    -- Build hp type: ∀ i j, i < sw.byteCount → j < lw.byteCount → a + ofNat i ≠ b + ofNat j
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
    let hp ← mkFreshExprMVar (some hpType)
    let proof ← try
      goal.withContext <| mkAppM ``VexISA.ByteMem_read_write_ne #[lw, sw, M, a, v, b, hp]
    catch e =>
      throwError "mem_frame: mkAppM failed: {e.toMessageData}"
    -- Discharge hp
    let mvars ← getMVars proof
    for mvar in mvars do
      if ← mvar.isAssigned then continue
      try
        setGoals [mvar]
        evalTactic (← `(tactic| (
          intro i j hi hj
          simp only [Width.byteCount] at hi hj
          (intro heq; have heq_nat := congrArg UInt64.toNat heq
           simp only [UInt64.toNat_add, UInt64.size, UInt64.toBitVec_toNat] at *
           omega))))
      catch _ =>
        let mvType ← mvar.getType
        throwError "mem_frame: could not discharge side condition:\n  {mvType}"
    -- Rewrite the goal
    let (newType, eqProof?) ← goal.withContext (rewriteFirst goalType lw sw M a v b proof)
    match eqProof? with
    | none => break
    | some eqProof =>
      progress := true
      let newGoal ← goal.replaceTargetEq newType eqProof
      replaceMainGoal [newGoal]
  unless progress do
    throwError "mem_frame: no ByteMem.read (ByteMem.write ...) patterns could be simplified"
