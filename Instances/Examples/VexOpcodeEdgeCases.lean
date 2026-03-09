import Instances.ISAs.VexLowerCore
import Instances.ISAs.VexConcrete
import Instances.ISAs.VexAmd64

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA

namespace Instances.Examples

private def edgeState : Amd64ConcreteState :=
  mkAmd64State 0 0 0 0 ByteMem.empty

private def emptyTemps : TempEnv := TempEnv.empty

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

private def add32OverflowEdge : Amd64Expr :=
  .add32 (.const 0xFFFF_FFFF) (.const 0x2)

example : evalExpr edgeState emptyTemps add32OverflowEdge = 0x1 := by
  native_decide

example :
    evalExpr edgeState emptyTemps add32OverflowEdge =
      evalSymExpr edgeState (lowerExpr SymSub.id SymTempEnv.empty add32OverflowEdge) := by
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
