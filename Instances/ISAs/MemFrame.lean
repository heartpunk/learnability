import Instances.ISAs.VexSyntax
import Lean

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

/-- Walk expression tree, find first read-of-write, return its components. -/
private partial def findReadOfWrite (e : Expr) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  if let some r := matchReadOfWrite? e.consumeMData then r
  else match e.consumeMData with
  | .app f x => findReadOfWrite f |>.orElse fun _ => findReadOfWrite x
  | _ => none

/-- Walk expression tree, rewriting first read-of-write with a given proof. -/
private partial def rewriteFirst (e : Expr) (lw sw M a v b proof : Expr) :
    MetaM (Expr × Option Expr) := do
  let ec := e.consumeMData
  if let some (lw', _, _, _, _, b') := matchReadOfWrite? ec then
    -- Check if this is the SAME match (by comparing lw, b pointers)
    if lw' == lw && b' == b then
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

/-- The `mem_frame` tactic. -/
elab "mem_frame" : tactic => do
  let mut fuel := 50
  let mut progress := false
  while fuel > 0 do
    fuel := fuel - 1
    let goal ← getMainGoal
    let goalType ← goal.getType
    -- Find first read-of-write in the goal
    let some (lw, sw, M, a, v, b) := findReadOfWrite goalType
      | break  -- no more patterns
    -- Create mvars for side conditions and build the proof
    let m1 ← mkFreshExprMVar none
    let m2 ← mkFreshExprMVar none
    let m3 ← mkFreshExprMVar none
    let proof ← try
      goal.withContext <| mkAppM ``ByteMem_read_write_nonoverlap #[lw, sw, M, a, v, b, m1, m2, m3]
    catch e =>
      throwError "mem_frame: failed to construct proof term"
    -- Discharge side conditions using simp + omega
    for mvar in [m1, m2, m3] do
      try
        setGoals [mvar.mvarId!]
        evalTactic (← `(tactic| (simp only [Width.byteCount, UInt64.size]; omega)))
      catch _ =>
        throwError "mem_frame: could not discharge side condition"
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
