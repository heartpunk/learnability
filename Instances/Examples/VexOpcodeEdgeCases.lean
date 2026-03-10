import Instances.ISAs.VexLowerCore
import Instances.ISAs.VexConcrete
import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

private def edgeState : Amd64ConcreteState :=
  mkAmd64State 0 0 0x0 0x0 0x0 0x0 0 0 ByteMem.empty

private def emptyTemps : TempEnv := TempEnv.empty

private def widthMem : ByteMem :=
  ByteMem.write64le ByteMem.empty 0x10 0x1122_3344_5566_7788

private def widthState : Amd64ConcreteState :=
  mkAmd64State 0 0 0x0 0x0 0x0 0x0 0 0 widthMem

private def narrow32Edge : Amd64Expr :=
  .narrow32 (.const 0x1234_5678_90AB_CDEF)

example : evalExpr edgeState emptyTemps narrow32Edge = 0x90AB_CDEF := by
  native_decide

example :
    evalExpr edgeState emptyTemps narrow32Edge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty narrow32Edge) := by
  native_decide

private def zext64Edge : Amd64Expr :=
  .zext64 (.const 0x1234_5678_90AB_CDEF)

example : evalExpr edgeState emptyTemps zext64Edge = 0x90AB_CDEF := by
  native_decide

example :
    evalExpr edgeState emptyTemps zext64Edge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty zext64Edge) := by
  native_decide

private def sext8to32NegativeEdge : Amd64Expr :=
  .sext8to32 (.const 0x80)

example : evalExpr edgeState emptyTemps sext8to32NegativeEdge = 0xFFFF_FF80 := by
  native_decide

example :
    evalExpr edgeState emptyTemps sext8to32NegativeEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty sext8to32NegativeEdge) := by
  native_decide

private def sext32to64NegativeEdge : Amd64Expr :=
  .sext32to64 (.const 0x1234_5678_FFFF_FF80)

example : evalExpr edgeState emptyTemps sext32to64NegativeEdge = 0xFFFF_FFFF_FFFF_FF80 := by
  native_decide

example :
    evalExpr edgeState emptyTemps sext32to64NegativeEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty sext32to64NegativeEdge) := by
  native_decide

private def add32OverflowEdge : Amd64Expr :=
  .add32 (.const 0xFFFF_FFFF) (.const 0x2)

example : evalExpr edgeState emptyTemps add32OverflowEdge = 0x1 := by
  native_decide

example :
    evalExpr edgeState emptyTemps add32OverflowEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty add32OverflowEdge) := by
  native_decide

private def sub32UnderflowEdge : Amd64Expr :=
  .sub32 (.const 0x0) (.const 0x1)

example : evalExpr edgeState emptyTemps sub32UnderflowEdge = 0xFFFF_FFFF := by
  native_decide

private def shl32AndMaskEdge : Amd64Expr :=
  .shl32 (.const 0x1) (.const 0x21)

example : evalExpr edgeState emptyTemps shl32AndMaskEdge = 0x2 := by
  native_decide

example :
    evalExpr edgeState emptyTemps shl32AndMaskEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty shl32AndMaskEdge) := by
  native_decide

example :
    evalExpr edgeState emptyTemps sub32UnderflowEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty sub32UnderflowEdge) := by
  native_decide

private def load16Edge : Amd64Expr :=
  .load .w16 (.const 0x10)

example : evalExpr widthState emptyTemps load16Edge = 0x7788 := by
  native_decide

example :
    evalExpr widthState emptyTemps load16Edge =
      evalSymExpr widthState (lowerExpr SymSub.id SymTempEnv.empty load16Edge) := by
  native_decide

private def load8MissingEdge : Amd64Expr :=
  .load .w8 (.const 0x80)

example : evalExpr edgeState emptyTemps load8MissingEdge = 0x0 := by
  native_decide

example :
    evalExpr edgeState emptyTemps load8MissingEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty load8MissingEdge) := by
  native_decide

private def load32Edge : Amd64Expr :=
  .load .w32 (.const 0x10)

example : evalExpr widthState emptyTemps load32Edge = 0x5566_7788 := by
  native_decide

example :
    evalExpr widthState emptyTemps load32Edge =
      evalSymExpr widthState (lowerExpr SymSub.id SymTempEnv.empty load32Edge) := by
  native_decide

example : ByteMem.write .w16 widthMem 0x10 0xABCD = ByteMem.write64le ByteMem.empty 0x10 0x1122_3344_5566_ABCD := by
  native_decide

example : ByteMem.write .w8 widthMem 0x10 0xABCD = ByteMem.write64le ByteMem.empty 0x10 0x1122_3344_5566_77CD := by
  native_decide

example : ByteMem.write .w32 widthMem 0x10 0xDEAD_BEEF = ByteMem.write64le ByteMem.empty 0x10 0x1122_3344_DEAD_BEEF := by
  native_decide

private def shl64ModuloEdge : Amd64Expr :=
  .shl64 (.const 0x1) (.const 0x41)

example : evalExpr edgeState emptyTemps shl64ModuloEdge = 0x2 := by
  native_decide

example :
    evalExpr edgeState emptyTemps shl64ModuloEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty shl64ModuloEdge) := by
  native_decide

private def shr64ModuloEdge : Amd64Expr :=
  .shr64 (.const 0x10) (.const 0x41)

example : evalExpr edgeState emptyTemps shr64ModuloEdge = 0x8 := by
  native_decide

example :
    evalExpr edgeState emptyTemps shr64ModuloEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty shr64ModuloEdge) := by
  native_decide

private def lt64UnsignedEdge : Amd64Cond :=
  .lt64 (.const 0x0) (.const 0xFFFF_FFFF_FFFF_FFFF)

example : evalCond edgeState emptyTemps lt64UnsignedEdge = true := by
  native_decide

example :
    evalCond edgeState emptyTemps lt64UnsignedEdge =
      evalSymPC edgeState (lowerCond SymSub.id SymTempEnv.empty lt64UnsignedEdge) := by
  native_decide

private def le64EqualityEdge : Amd64Cond :=
  .le64 (.const 0xFFFF_FFFF_FFFF_FFFF) (.const 0xFFFF_FFFF_FFFF_FFFF)

example : evalCond edgeState emptyTemps le64EqualityEdge = true := by
  native_decide

example :
    evalCond edgeState emptyTemps le64EqualityEdge =
      evalSymPC edgeState (lowerCond SymSub.id SymTempEnv.empty le64EqualityEdge) := by
  native_decide

end Instances.Examples
