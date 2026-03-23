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

/-- Lower S (sign) flag: bit 31 of the 32-bit result is set. -/
def lowerAmd64CalculateConditionSign {Reg : Type}
    (ccOp ccDep1 ccDep2 : SymExpr Reg) : SymPC Reg :=
  -- Sign flag = bit 31 of result. We test: (result &&& 0x80000000) != 0
  -- which is equivalent to: NOT (result &&& 0x80000000 == 0)
  let subCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x7))
      (.not (.eq (.and64 (.uext32 (.sub64 (.low32 ccDep1) (.low32 ccDep2))) (.const 0x80000000)) (.const 0)))
  let addCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x3))
      (.not (.eq (.and64 (.uext32 (.add64 (.low32 ccDep1) (.low32 ccDep2))) (.const 0x80000000)) (.const 0)))
  let logicCase : SymPC Reg :=
    .and (.eq ccOp (.const 0x13))
      (.not (.eq (.and64 (.low32 ccDep1) (.const 0x80000000)) (.const 0)))
  pcOr subCase (pcOr addCase logicCase)

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

/-- Eagerly fold constant-constant operations during lowering.
    Prevents exponential expression growth when temps form long chains
    of constant computations (e.g., array initialization loops). -/
@[simp, inline] def foldBin64 {Reg : Type}
    (op : SymExpr Reg → SymExpr Reg → SymExpr Reg)
    (f : UInt64 → UInt64 → UInt64)
    (a b : SymExpr Reg) : SymExpr Reg :=
  match a, b with
  | .const x, .const y => .const (f x y)
  | _, _ => op a b

@[simp, inline] def foldBin32 {Reg : Type}
    (op : SymExpr Reg → SymExpr Reg → SymExpr Reg)
    (f : UInt64 → UInt64 → UInt64)
    (a b : SymExpr Reg) : SymExpr Reg :=
  match a, b with
  | .const x, .const y => .const (f x y)
  | _, _ => op a b

@[simp, inline] def foldUn {Reg : Type}
    (op : SymExpr Reg → SymExpr Reg)
    (f : UInt64 → UInt64)
    (a : SymExpr Reg) : SymExpr Reg :=
  match a with
  | .const x => .const (f x)
  | _ => op a

def lowerExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Expr Reg → SymExpr Reg
  | .const value => .const value
  | .get reg => sub.regs reg
  | .tmp tmp => temps.get tmp
  | .narrow32 expr => foldUn .low32 mask32 (lowerExpr sub temps expr)
  | .zext64 expr => foldUn .uext32 mask32 (lowerExpr sub temps expr)
  | .sext8to32 expr => .sext8to32 (lowerExpr sub temps expr)
  | .sext32to64 expr => .sext32to64 (lowerExpr sub temps expr)
  | .add32 lhs rhs =>
      let l := lowerExpr sub temps lhs
      let r := lowerExpr sub temps rhs
      match l, r with
      | .const x, .const y => .const (mask32 (x + y))
      | _, _ => .uext32 (.add64 l r)
  | .sub32 lhs rhs => foldBin32 .sub32 (fun x y => mask32 (x - y)) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .shl32 lhs rhs => foldBin32 .shl32 shiftLeft32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .and32 lhs rhs => foldBin32 .and32 (fun x y => mask32 (x &&& y)) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .or32 lhs rhs => foldBin32 .or32 (fun x y => mask32 (x ||| y)) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .xor32 lhs rhs => foldBin32 .xor32 (fun x y => mask32 (x ^^^ y)) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .add64 lhs rhs => foldBin64 .add64 (· + ·) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .sub64 lhs rhs => foldBin64 .sub64 (· - ·) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .xor64 lhs rhs => foldBin64 .xor64 (· ^^^ ·) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .and64 lhs rhs => foldBin64 .and64 (· &&& ·) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .or64 lhs rhs => foldBin64 .or64 (· ||| ·) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .shl64 lhs rhs => foldBin64 .shl64 shiftLeft64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .shr64 lhs rhs => foldBin64 .shr64 shiftRight64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .mul64 lhs rhs => foldBin64 .mul64 (· * ·) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .mul32 lhs rhs => foldBin32 .mul32 (fun x y => mask32 (x * y)) (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .not64 x => foldUn .not64 (~~~ ·) (lowerExpr sub temps x)
  | .not32 x => foldUn .not32 (fun v => mask32 (~~~ v)) (lowerExpr sub temps x)
  | .sar64 lhs rhs => .sar64 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .sar32 lhs rhs => .sar32 (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .ite cond t f => .ite (lowerExpr sub temps cond) (lowerExpr sub temps t) (lowerExpr sub temps f)
  | .load width addr => .load width sub.mem (lowerExpr sub temps addr)

def lowerCond {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (temps : SymTempEnv Reg) : Cond Reg → SymPC Reg
  | .eq64 lhs rhs => .eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .lt64 lhs rhs => .lt (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .le64 lhs rhs => .le (lowerExpr sub temps lhs) (lowerExpr sub temps rhs)
  | .ne64 lhs rhs => .not (.eq (lowerExpr sub temps lhs) (lowerExpr sub temps rhs))
  | .amd64CalculateCondition code ccOp ccDep1 ccDep2 _ccNdep =>
      let op := lowerExpr sub temps ccOp
      let d1 := lowerExpr sub temps ccDep1
      let d2 := lowerExpr sub temps ccDep2
      if code = 0x4 then lowerAmd64CalculateConditionZero op d1 d2
      else if code = 0x8 then lowerAmd64CalculateConditionSign op d1 d2
      else if code = 0x9 then .not (lowerAmd64CalculateConditionSign op d1 d2)
      else .not .true

end VexISA
