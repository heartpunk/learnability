import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexBridgeCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def lowerStmt {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) : LowerState Reg → Stmt Reg → LowerState Reg
  | state, .linear stmt =>
      lowerLinearStmt state stmt
  | state, .branch stmt =>
      lowerBranchContinue ip_reg state stmt

def lowerStmts {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (stmts : List (Stmt Reg)) : LowerState Reg :=
  stmts.foldl (lowerStmt ip_reg) (SymSub.id, SymTempEnv.empty)

def lowerBlockSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) : SymSub Reg :=
  SymSub.write (lowerStmts block.ip_reg block.stmts).1 block.ip_reg (.const block.next)

def lowerBlock {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) : Summary Reg :=
  { sub := lowerBlockSub block
  , pc := .true }

def lowerSummariesFrom {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (ps : PartialSummary Reg) : List (Stmt Reg) → UInt64 → List (Summary Reg)
  | [], next =>
      [ps.finish ip_reg next]
  | .linear stmt :: stmts, next =>
      let lowered := lowerLinearStmt (ps.sub, ps.temps) stmt
      lowerSummariesFrom ip_reg
        { ps with sub := lowered.1, temps := lowered.2 }
        stmts next
  | .branch stmt :: stmts, next =>
      let bridge := branchStmtBridge ip_reg stmt
      bridge.lowerTaken ps ::
      lowerSummariesFrom ip_reg (bridge.lowerContinue ps) stmts next

def lowerBlockSummariesList {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) : List (Summary Reg) :=
  lowerSummariesFrom block.ip_reg PartialSummary.init block.stmts block.next

def lowerBlockSummaries {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) : Finset (Summary Reg) :=
  (lowerBlockSummariesList block).toFinset

end VexISA
