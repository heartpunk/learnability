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
    -- Construct the proof term directly: ByteMem_read_write_nonoverlap lw sw M a v b h_a h_b h
    -- Create typed mvars for the 3 hypothesis args
    let uint64SizeExpr := mkConst ``UInt64.size
    let natExpr := mkConst ``Nat
    let propSort := mkSort .zero
    -- h_a type: a.toNat + sw.byteCount ≤ UInt64.size
    let h_a_type ← goal.withContext <| do
      let aToNat ← mkAppM ``UInt64.toNat #[a]
      let swBC ← mkAppM ``Width.byteCount #[sw]
      let lhs ← mkAppM ``HAdd.hAdd #[aToNat, swBC]
      mkAppM ``LE.le #[lhs, uint64SizeExpr]
    -- h_b type: b.toNat + lw.byteCount ≤ UInt64.size
    let h_b_type ← goal.withContext <| do
      let bToNat ← mkAppM ``UInt64.toNat #[b]
      let lwBC ← mkAppM ``Width.byteCount #[lw]
      let lhs ← mkAppM ``HAdd.hAdd #[bToNat, lwBC]
      mkAppM ``LE.le #[lhs, uint64SizeExpr]
    -- h type: a.toNat + sw.byteCount ≤ b.toNat ∨ b.toNat + lw.byteCount ≤ a.toNat
    let h_type ← goal.withContext <| do
      let aToNat ← mkAppM ``UInt64.toNat #[a]
      let bToNat ← mkAppM ``UInt64.toNat #[b]
      let swBC ← mkAppM ``Width.byteCount #[sw]
      let lwBC ← mkAppM ``Width.byteCount #[lw]
      let lhs1 ← mkAppM ``HAdd.hAdd #[aToNat, swBC]
      let lhs2 ← mkAppM ``HAdd.hAdd #[bToNat, lwBC]
      let left ← mkAppM ``LE.le #[lhs1, bToNat]
      let right ← mkAppM ``LE.le #[lhs2, aToNat]
      mkAppM ``Or #[left, right]
    let m1 ← mkFreshExprMVar (some h_a_type)
    let m2 ← mkFreshExprMVar (some h_b_type)
    let m3 ← mkFreshExprMVar (some h_type)
    let proof ← try
      goal.withContext <| mkAppM ``VexISA.ByteMem_read_write_nonoverlap #[lw, sw, M, a, v, b, m1, m2, m3]
    catch e =>
      throwError "mem_frame: mkAppM failed: {e.toMessageData}"
    -- Find and discharge the 3 mvar side conditions
    let mvars ← getMVars proof
    for mvar in mvars do
      if ← mvar.isAssigned then continue
      try
        setGoals [mvar]
        -- Try multiple strategies to discharge
        evalTactic (← `(tactic| first
          | (simp only [Width.byteCount, UInt64.size]; omega)
          | (simp_all only [Width.byteCount, UInt64.size, UInt64.toNat_add,
              UInt64.toBitVec_toNat, _root_.UInt64.toNat_sub_of_le]; omega)
          | (simp only [Width.byteCount]; bv_omega)
          | assumption))
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
