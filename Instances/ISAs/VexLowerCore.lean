import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

def pcOr {Reg : Type} (φ ψ : SymPC Reg) : SymPC Reg :=
  .not (.and (.not φ) (.not ψ))

def lowerAmd64CalculateConditionZero {Reg : Type}
    (ccOp ccDep1 ccDep2 : SymExpr Reg) : SymPC Reg :=
  let addCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x3))
      (.eq (.uext32 (.add64 (.low32 ccDep1) (.low32 ccDep2))) (.const 0))
  let subCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x7))
      (.eq (.low32 ccDep1) (.low32 ccDep2))
  let logicCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x13))
      (.eq (.low32 ccDep1) (.const 0))
  pcOr addCase (pcOr subCase logicCase)

structure PartialSummary (Reg : Type) where
  sub : SymSub Reg
  pc : SymPC Reg
  temps : SymTempEnv Reg

def PartialSummary.init {Reg : Type} : PartialSummary Reg :=
  { sub := SymSub.id
  , pc := .true
  , temps := SymTempEnv.empty }

def PartialSummary.finish {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ps : PartialSummary Reg) (ip_reg : Reg) (next : UInt64) : Summary Reg :=
  -- next=0 is the sentinel for Ijk_Ret/indirect branches: ip_reg is already
  -- encoded in ps.sub via a `put ip_reg (tmp n)` stmt added by the parser.
  -- Avoid overwriting that entry with a spurious write of 0.
  { sub := if next = 0 then ps.sub else SymSub.write ps.sub ip_reg (.const next)
  , pc := ps.pc }

abbrev LowerState (Reg : Type) := SymSub Reg × SymTempEnv Reg

def lowerExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Expr Reg → SymExpr Reg
  | .const value => .const value
  | .get reg => sub.regs reg
  | .tmp tmp => temps tmp
  | .narrow32 expr => .low32 (lowerExpr sub temps expr)
  | .zext64 expr => .uext32 (lowerExpr sub temps expr)
  | .sext8to32 expr => .sext8to32 (lowerExpr sub temps expr)
  | .sext32to64 expr => .sext32to64 (lowerExpr sub temps expr)
  | .add32 lhs rhs => .uext32 (.add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs))
  | .sub32 lhs rhs => .sub32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .shl32 lhs rhs => .shl32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .and32 lhs rhs => .and32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .or32 lhs rhs => .or32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .xor32 lhs rhs => .xor32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .add64 lhs rhs => .add64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .sub64 lhs rhs => .sub64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .xor64 lhs rhs => .xor64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .and64 lhs rhs => .and64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .or64 lhs rhs => .or64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .shl64 lhs rhs => .shl64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .shr64 lhs rhs => .shr64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .mul64 lhs rhs => .mul64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .load width addr => .load width sub.mem (lowerExpr sub temps addr)

def lowerCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Cond Reg → SymPC Reg
  | .eq64 lhs rhs => .eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .lt64 lhs rhs => .lt (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .le64 lhs rhs => .le (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .ne64 lhs rhs => .not (.eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs))
  | .amd64CalculateCondition code ccOp ccDep1 ccDep2 _ccNdep =>
      if code = 0x4 then
        lowerAmd64CalculateConditionZero
          (lowerExpr sub temps ccOp)
          (lowerExpr sub temps ccDep1)
          (lowerExpr sub temps ccDep2)
      else
        .not .true

end VexISA
