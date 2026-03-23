import Instances.ISAs.VexSyntax
import Lean

/-!
# mem_frame tactic

Automates ByteMem read-after-write frame reasoning by walking the goal
expression tree and peeling non-overlapping writes from reads.
Uses ByteMem_read_write_ne with pointwise address distinctness.
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

/-- Walk expression tree, find DEEPEST read-of-write (innermost first). -/
private partial def findReadOfWrite (e : Expr) :
    Option (Expr × Expr × Expr × Expr × Expr × Expr) :=
  -- First recurse into children to find deeper matches
  let deeper := match e.consumeMData with
    | .app f x => findReadOfWrite f |>.orElse fun _ => findReadOfWrite x
    | _ => none
  -- If a deeper match exists, use it. Otherwise check this node.
  deeper.orElse fun _ => matchReadOfWrite? e.consumeMData

/-- Walk expression tree, rewriting first read-of-write with a given proof. -/
private partial def rewriteFirst (e : Expr) (lw sw M a v b proof : Expr) :
    MetaM (Expr × Option Expr) := do
  let ec := e.consumeMData
  if let some (lw', _, _, _, _, b') := matchReadOfWrite? ec then
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
    let some (lw, sw, M, a, v, b) := findReadOfWrite goalType
      | break
    -- Build hp type matching ByteMem_read_write_ne's signature exactly:
    -- ∀ (i : Nat) (j : Nat), i < sw.byteCount → j < lw.byteCount → a + ofNat i ≠ b + ofNat j
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
        -- Build: i < swBC → j < lwBC → neq
        let body ← mkArrow hj neq
        let body ← mkArrow hi body
        -- Build: ∀ (j : Nat), ...
        let body ← mkForallFVars #[j] body
        mkForallFVars #[i] body
    let hp ← mkFreshExprMVar (some hpType)
    let proof ← try
      goal.withContext <| mkAppM ``VexISA.ByteMem_read_write_ne #[lw, sw, M, a, v, b, hp]
    catch e =>
      throwError "mem_frame: mkAppM failed: {e.toMessageData}"
    -- Find and discharge the hp mvar
    let mvars ← getMVars proof
    for mvar in mvars do
      if ← mvar.isAssigned then continue
      try
        setGoals [mvar]
        -- The hp condition is: ∀ i j, i < sw.byteCount → j < lw.byteCount → a + ofNat i ≠ b + ofNat j
        -- Discharge by intro + native_decide (for concrete) or simp_all + omega (for symbolic)
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
