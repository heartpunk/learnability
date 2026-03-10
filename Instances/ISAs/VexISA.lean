import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexBridgeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

@[simp] def execStmt {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) : ConcreteState Reg × TempEnv → Stmt Reg → ConcreteState Reg × TempEnv
  | cfg, .linear stmt =>
      execLinearStmt cfg stmt
  | cfg, .branch stmt =>
      execBranchContinue ip_reg cfg stmt

@[simp] def execBlock {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input : ConcreteState Reg) : ConcreteState Reg :=
  let (state, _) := block.stmts.foldl (execStmt block.ip_reg) (input, TempEnv.empty)
  state.write block.ip_reg block.next

/-- Ordered concrete successor semantics for the current VEX block slice.

`Exit` short-circuits: the first enabled exit wins and fallthrough is discarded.
The `Finset` result is for alignment with summary families, not to model
general nondeterministic CFG branching. -/
@[simp] def execStmtsSuccs {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (fallthrough : UInt64) :
    List (Stmt Reg) → ConcreteState Reg × TempEnv → Finset (ConcreteState Reg)
  | [], (state, _) =>
      -- fallthrough=0 is the sentinel for Ijk_Ret and indirect branches: ip_reg
      -- is already set by the preceding stmts (e.g. `put rip (tmp n)` for Ijk_Ret).
      -- Return the state as-is; an extra write of 0 would clobber the result.
      if fallthrough == 0 then { state } else { state.write ip_reg fallthrough }
  | stmt :: stmts, cfg =>
      match stmt with
      | .linear stmt =>
          execStmtsSuccs ip_reg fallthrough stmts (execLinearStmt cfg stmt)
      | .branch stmt =>
          let bridge := branchStmtBridge ip_reg stmt
          if bridge.fires cfg then
            { bridge.taken cfg }
          else
            execStmtsSuccs ip_reg fallthrough stmts (bridge.cont cfg)

@[simp] def execBlockSuccs {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) (input : ConcreteState Reg) : Finset (ConcreteState Reg) :=
  execStmtsSuccs block.ip_reg block.next block.stmts (input, TempEnv.empty)

end VexISA
