import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def evalAmd64CalculateConditionZero
    (ccOp ccDep1 ccDep2 _ccNdep : UInt64) : Bool :=
  if ccOp = 0x3 then
    mask32 (mask32 ccDep1 + mask32 ccDep2) == 0
  else if ccOp = 0x7 then
    mask32 ccDep1 == mask32 ccDep2
  else if ccOp = 0x13 then
    mask32 ccDep1 == 0
  else
    false

/-- AMD64 S (sign) flag: bit 31 of the result. -/
def evalAmd64CalculateConditionSign
    (ccOp ccDep1 ccDep2 _ccNdep : UInt64) : Bool :=
  if ccOp = 0x7 then       -- SUB32: sign of (dep1 - dep2)
    mask32 (mask32 ccDep1 - mask32 ccDep2) &&& 0x80000000 != 0
  else if ccOp = 0x3 then  -- ADD32: sign of (dep1 + dep2)
    mask32 (mask32 ccDep1 + mask32 ccDep2) &&& 0x80000000 != 0
  else if ccOp = 0x13 then -- LOGIC32: sign of result
    mask32 ccDep1 &&& 0x80000000 != 0
  else
    false

/-- AMD64 B (below, unsigned): CF=1. For SUB32: unsigned dep1 < dep2. -/
def evalAmd64CalculateConditionB
    (ccOp ccDep1 ccDep2 _ccNdep : UInt64) : Bool :=
  if ccOp = 0x7 then decide (mask32 ccDep1 < mask32 ccDep2)
  else false

/-- AMD64 LE (less or equal, signed): ZF=1 or SF≠OF. For SUB32: signed dep1 ≤ dep2. -/
def evalAmd64CalculateConditionLE
    (ccOp ccDep1 ccDep2 _ccNdep : UInt64) : Bool :=
  if ccOp = 0x7 then       -- SUB32: signed ≤
    decide (signExtend32to64 (mask32 ccDep1) ≤ signExtend32to64 (mask32 ccDep2))
  else
    false

@[simp] def evalExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (temps : TempEnv) : Expr Reg → UInt64
  | .const value => value
  | .get reg => state.read reg
  | .tmp tmp => temps tmp
  | .narrow32 expr => mask32 (evalExpr state temps expr)
  | .zext64 expr => mask32 (evalExpr state temps expr)
  | .sext8to32 expr => signExtend8to32 (evalExpr state temps expr)
  | .sext32to64 expr => signExtend32to64 (evalExpr state temps expr)
  | .add32 lhs rhs => mask32 (evalExpr state temps lhs + evalExpr state temps rhs)
  | .sub32 lhs rhs => mask32 (evalExpr state temps lhs - evalExpr state temps rhs)
  | .shl32 lhs rhs => shiftLeft32 (evalExpr state temps lhs) (evalExpr state temps rhs)
  | .and32 lhs rhs => mask32 (evalExpr state temps lhs &&& evalExpr state temps rhs)
  | .or32 lhs rhs => mask32 (evalExpr state temps lhs ||| evalExpr state temps rhs)
  | .xor32 lhs rhs => mask32 (evalExpr state temps lhs ^^^ evalExpr state temps rhs)
  | .add64 lhs rhs => evalExpr state temps lhs + evalExpr state temps rhs
  | .sub64 lhs rhs => evalExpr state temps lhs - evalExpr state temps rhs
  | .xor64 lhs rhs => evalExpr state temps lhs ^^^ evalExpr state temps rhs
  | .and64 lhs rhs => evalExpr state temps lhs &&& evalExpr state temps rhs
  | .or64 lhs rhs => evalExpr state temps lhs ||| evalExpr state temps rhs
  | .shl64 lhs rhs => shiftLeft64 (evalExpr state temps lhs) (evalExpr state temps rhs)
  | .shr64 lhs rhs => shiftRight64 (evalExpr state temps lhs) (evalExpr state temps rhs)
  | .mul64 lhs rhs => evalExpr state temps lhs * evalExpr state temps rhs
  | .mul32 lhs rhs => mask32 (evalExpr state temps lhs * evalExpr state temps rhs)
  | .not64 x => ~~~(evalExpr state temps x)
  | .not32 x => mask32 (~~~(evalExpr state temps x))
  | .sar64 lhs rhs => signedShiftRight64 (evalExpr state temps lhs) (evalExpr state temps rhs)
  | .sar32 lhs rhs => signedShiftRight32 (evalExpr state temps lhs) (evalExpr state temps rhs)
  | .ite cond t f => if evalExpr state temps cond != 0 then evalExpr state temps t else evalExpr state temps f
  | .load width addr => ByteMem.read width state.mem (evalExpr state temps addr)

@[simp] def evalCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (temps : TempEnv) : Cond Reg → Bool
  | .eq64 lhs rhs => evalExpr state temps lhs == evalExpr state temps rhs
  | .lt64 lhs rhs => decide (evalExpr state temps lhs < evalExpr state temps rhs)
  | .le64 lhs rhs => decide (evalExpr state temps lhs ≤ evalExpr state temps rhs)
  | .ne64 lhs rhs => !(evalExpr state temps lhs == evalExpr state temps rhs)
  | .amd64CalculateCondition code ccOp ccDep1 ccDep2 ccNdep =>
      let op := evalExpr state temps ccOp
      let d1 := evalExpr state temps ccDep1
      let d2 := evalExpr state temps ccDep2
      let nd := evalExpr state temps ccNdep
      if code = 0x4 then evalAmd64CalculateConditionZero op d1 d2 nd
      else if code = 0x8 then evalAmd64CalculateConditionSign op d1 d2 nd
      else if code = 0x9 then !evalAmd64CalculateConditionSign op d1 d2 nd
      else if code = 0x2 then evalAmd64CalculateConditionB op d1 d2 nd
      else if code = 0x3 then !evalAmd64CalculateConditionB op d1 d2 nd
      else if code = 0xE then evalAmd64CalculateConditionLE op d1 d2 nd
      else if code = 0xF then !evalAmd64CalculateConditionLE op d1 d2 nd
      else false

end VexISA
