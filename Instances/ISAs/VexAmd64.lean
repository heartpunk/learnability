import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

inductive Amd64Reg where
  | rax
  | rcx
  | rdx
  | rsi
  | rbp
  | rsp
  | rdi
  | rip
  | cc_op
  | cc_dep1
  | cc_dep2
  | cc_ndep
  | r11
  | rbx
  | r8
  | r9
  | r12
  deriving DecidableEq, Repr

instance : Hashable Amd64Reg where
  hash
    | .rax => 0 | .rcx => 1 | .rdx => 2 | .rsi => 3
    | .rbp => 4 | .rsp => 5 | .rdi => 6 | .rip => 7
    | .cc_op => 8 | .cc_dep1 => 9 | .cc_dep2 => 10 | .cc_ndep => 11
    | .r11 => 12
    | .rbx => 13
    | .r8 => 14
    | .r9 => 15
    | .r12 => 16

instance : EnumReg Amd64Reg where
  allRegs := [.rax, .rcx, .rdx, .rsi, .rbp, .rsp, .rdi, .rip, .cc_op, .cc_dep1, .cc_dep2, .cc_ndep, .r11, .rbx, .r8, .r9, .r12]

instance : Fintype Amd64Reg :=
  ⟨{.rax, .rcx, .rdx, .rsi, .rbp, .rsp, .rdi, .rip, .cc_op, .cc_dep1, .cc_dep2, .cc_ndep, .r11, .rbx, .r8, .r9, .r12}, by
    intro reg
    cases reg <;> simp⟩

abbrev Amd64Block := Block Amd64Reg
abbrev Amd64Expr := Expr Amd64Reg
abbrev Amd64Cond := Cond Amd64Reg
abbrev Amd64Stmt := Stmt Amd64Reg
abbrev Amd64LinearStmt := LinearStmt Amd64Reg
abbrev Amd64BranchStmt := BranchStmt Amd64Reg
abbrev Amd64ConcreteState := ConcreteState Amd64Reg

def mkAmd64Block (stmts : List Amd64Stmt) (next : UInt64) : Amd64Block :=
  { stmts := stmts, ip_reg := .rip, next := next }

def mkAmd64StateCC
    (rax rcx rdx rsi rbp rsp rdi rip cc_op cc_dep1 cc_dep2 cc_ndep : UInt64) (mem : ByteMem) : Amd64ConcreteState :=
  { regs := fun
      | .rax => rax
      | .rcx => rcx
      | .rdx => rdx
      | .rsi => rsi
      | .rbp => rbp
      | .rsp => rsp
      | .rdi => rdi
      | .rip => rip
      | .cc_op => cc_op
      | .cc_dep1 => cc_dep1
      | .cc_dep2 => cc_dep2
      | .cc_ndep => cc_ndep
      | .r11 => 0
      | .rbx => 0
      | .r8 => 0
      | .r9 => 0
      | .r12 => 0
  , mem := mem }

def mkAmd64State (rax rcx rdx rsi rbp rsp rdi rip : UInt64) (mem : ByteMem) : Amd64ConcreteState :=
  mkAmd64StateCC rax rcx rdx rsi rbp rsp rdi rip 0 0 0 0 mem

instance : Repr Amd64ConcreteState where
  reprPrec state _ :=
    repr
      ( state.read .rax
      , state.read .rcx
      , state.read .rdx
      , state.read .rsi
      , state.read .rbp
      , state.read .rsp
      , state.read .rdi
      , state.read .rip
      , state.read .cc_op
      , state.read .cc_dep1
      , state.read .cc_dep2
      , state.read .cc_ndep
      , state.read .r11
      , state.read .rbx
      , state.read .r8
      , state.read .r9
      , state.read .r12
      , state.mem
      )

end VexISA
