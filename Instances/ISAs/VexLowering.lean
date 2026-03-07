import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA


def lowerExpr (sub : SymSub) (temps : SymTempEnv) : Expr → SymExpr
  | .const value => .const value
  | .get reg => sub reg
  | .tmp tmp => temps tmp
  | .add64 lhs rhs => .add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)

abbrev LowerState := SymSub × SymTempEnv


def lowerStmt : LowerState → Stmt → LowerState
  | (sub, temps), .wrTmp tmp expr =>
      (sub, SymTempEnv.write temps tmp (lowerExpr sub temps expr))
  | (sub, temps), .put reg expr =>
      (SymSub.write sub reg (lowerExpr sub temps expr), temps)


def lowerStmts (stmts : List Stmt) : LowerState :=
  stmts.foldl lowerStmt (SymSub.id, SymTempEnv.empty)


def lowerBlockSub (block : Block) : SymSub :=
  SymSub.write (lowerStmts block.stmts).1 .rip (.const block.next)


def lowerBlock (block : Block) : Summary :=
  { sub := lowerBlockSub block
  , pc := .true }

end VexISA
