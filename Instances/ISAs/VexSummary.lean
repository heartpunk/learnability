import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexSyntax

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

mutual
inductive SymExpr (Reg : Type) where
  | const : UInt64 → SymExpr Reg
  | reg : Reg → SymExpr Reg
  | low32 : SymExpr Reg → SymExpr Reg
  | uext32 : SymExpr Reg → SymExpr Reg
  | sext8to32 : SymExpr Reg → SymExpr Reg
  | sext32to64 : SymExpr Reg → SymExpr Reg
  | sub32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | shl32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | and32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | or32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | xor32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | add64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | sub64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | xor64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | and64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | or64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | shl64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | shr64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | mul64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | mul32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | not64 : SymExpr Reg → SymExpr Reg
  | not32 : SymExpr Reg → SymExpr Reg
  | sar64 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | sar32 : SymExpr Reg → SymExpr Reg → SymExpr Reg
  | ite : SymExpr Reg → SymExpr Reg → SymExpr Reg → SymExpr Reg
  | load : Width → SymMem Reg → SymExpr Reg → SymExpr Reg
  deriving DecidableEq, Repr

inductive SymMem (Reg : Type) where
  | base
  | store : Width → SymMem Reg → SymExpr Reg → SymExpr Reg → SymMem Reg
  deriving DecidableEq, Repr
end

inductive SymPC (Reg : Type) where
  | true
  | eq : SymExpr Reg → SymExpr Reg → SymPC Reg
  | lt : SymExpr Reg → SymExpr Reg → SymPC Reg
  | le : SymExpr Reg → SymExpr Reg → SymPC Reg
  | and : SymPC Reg → SymPC Reg → SymPC Reg
  | not : SymPC Reg → SymPC Reg
  deriving DecidableEq, Repr

structure SymSub (Reg : Type) where
  regs : Reg → SymExpr Reg
  mem : SymMem Reg

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (SymSub Reg) := by
  intro sub₁ sub₂
  by_cases hRegs : sub₁.regs = sub₂.regs
  · by_cases hMem : sub₁.mem = sub₂.mem
    · cases sub₁
      cases sub₂
      cases hRegs
      cases hMem
      exact isTrue rfl
    · exact isFalse (fun h => hMem (congrArg SymSub.mem h))
  · exact isFalse (fun h => hRegs (congrArg SymSub.regs h))

abbrev SymTempEnv (Reg : Type) := Std.HashMap Nat (SymExpr Reg)

structure Summary (Reg : Type) where
  sub : SymSub Reg
  pc : SymPC Reg

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (Summary Reg) := by
  intro summary₁ summary₂
  by_cases hSub : summary₁.sub = summary₂.sub
  · by_cases hPc : summary₁.pc = summary₂.pc
    · cases summary₁
      cases summary₂
      cases hSub
      cases hPc
      exact isTrue rfl
    · exact isFalse (fun h => hPc (congrArg Summary.pc h))
  · exact isFalse (fun h => hSub (congrArg Summary.sub h))

@[ext] theorem SymSub.ext {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {sub₁ sub₂ : SymSub Reg}
    (hRegs : sub₁.regs = sub₂.regs) (hMem : sub₁.mem = sub₂.mem) :
    sub₁ = sub₂ := by
  cases sub₁
  cases sub₂
  cases hRegs
  cases hMem
  rfl


def SymSub.id {Reg : Type} : SymSub Reg :=
  { regs := SymExpr.reg
  , mem := .base }


def SymSub.write {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (reg : Reg) (expr : SymExpr Reg) : SymSub Reg :=
  { sub with regs := fun reg' => if reg' = reg then expr else sub.regs reg' }


def SymSub.writeMem {Reg : Type} (sub : SymSub Reg) (mem : SymMem Reg) : SymSub Reg :=
  { sub with mem := mem }

@[simp] theorem SymSub.write_same {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (reg : Reg) (expr : SymExpr Reg) :
    (SymSub.write sub reg expr).regs reg = expr := by
  simp [SymSub.write]

@[simp] theorem SymSub.write_other {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) {reg reg' : Reg} (expr : SymExpr Reg)
    (h : reg' ≠ reg) : (SymSub.write sub reg expr).regs reg' = sub.regs reg' := by
  simp [SymSub.write, h]


def SymTempEnv.empty {Reg : Type} : SymTempEnv Reg := {}

@[inline] def SymTempEnv.get {Reg : Type} (temps : SymTempEnv Reg) (tmp : Nat) : SymExpr Reg :=
  temps.getD tmp (.const 0)

@[inline] def SymTempEnv.write {Reg : Type}
    (temps : SymTempEnv Reg) (tmp : Nat) (expr : SymExpr Reg) : SymTempEnv Reg :=
  temps.insert tmp expr

@[simp] theorem SymTempEnv.get_write_same {Reg : Type}
    (temps : SymTempEnv Reg) (tmp : Nat) (expr : SymExpr Reg) :
    (SymTempEnv.write temps tmp expr).get tmp = expr := by
  simp [SymTempEnv.get, SymTempEnv.write]

@[simp] theorem SymTempEnv.get_write_other {Reg : Type}
    (temps : SymTempEnv Reg) {tmp tmp' : Nat} (expr : SymExpr Reg)
    (h : tmp' ≠ tmp) : (SymTempEnv.write temps tmp expr).get tmp' = temps.get tmp' := by
  unfold SymTempEnv.get SymTempEnv.write
  simp [Std.HashMap.getD_insert, Ne.symm h]

@[simp] theorem SymTempEnv.get_empty {Reg : Type} (tmp : Nat) :
    (SymTempEnv.empty : SymTempEnv Reg).get tmp = .const 0 := by
  simp [SymTempEnv.get, SymTempEnv.empty]

mutual
@[simp] def evalSymExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) : SymExpr Reg → UInt64
  | .const value => value
  | .reg reg => state.read reg
  | .low32 expr => mask32 (evalSymExpr state expr)
  | .uext32 expr => mask32 (evalSymExpr state expr)
  | .sext8to32 expr => signExtend8to32 (evalSymExpr state expr)
  | .sext32to64 expr => signExtend32to64 (evalSymExpr state expr)
  | .sub32 lhs rhs => mask32 (evalSymExpr state lhs - evalSymExpr state rhs)
  | .shl32 lhs rhs => shiftLeft32 (evalSymExpr state lhs) (evalSymExpr state rhs)
  | .and32 lhs rhs => mask32 (evalSymExpr state lhs &&& evalSymExpr state rhs)
  | .or32 lhs rhs => mask32 (evalSymExpr state lhs ||| evalSymExpr state rhs)
  | .xor32 lhs rhs => mask32 (evalSymExpr state lhs ^^^ evalSymExpr state rhs)
  | .add64 lhs rhs => evalSymExpr state lhs + evalSymExpr state rhs
  | .sub64 lhs rhs => evalSymExpr state lhs - evalSymExpr state rhs
  | .xor64 lhs rhs => evalSymExpr state lhs ^^^ evalSymExpr state rhs
  | .and64 lhs rhs => evalSymExpr state lhs &&& evalSymExpr state rhs
  | .or64 lhs rhs => evalSymExpr state lhs ||| evalSymExpr state rhs
  | .shl64 lhs rhs => shiftLeft64 (evalSymExpr state lhs) (evalSymExpr state rhs)
  | .shr64 lhs rhs => shiftRight64 (evalSymExpr state lhs) (evalSymExpr state rhs)
  | .mul64 lhs rhs => evalSymExpr state lhs * evalSymExpr state rhs
  | .mul32 lhs rhs => mask32 (evalSymExpr state lhs * evalSymExpr state rhs)
  | .not64 x => ~~~(evalSymExpr state x)
  | .not32 x => mask32 (~~~(evalSymExpr state x))
  | .sar64 lhs rhs => signedShiftRight64 (evalSymExpr state lhs) (evalSymExpr state rhs)
  | .sar32 lhs rhs => signedShiftRight32 (evalSymExpr state lhs) (evalSymExpr state rhs)
  | .ite cond t f => if evalSymExpr state cond != 0 then evalSymExpr state t else evalSymExpr state f
  | .load width mem addr => ByteMem.read width (evalSymMem state mem) (evalSymExpr state addr)

@[simp] def evalSymMem {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) : SymMem Reg → ByteMem
  | .base => state.mem
  | .store width mem addr value =>
      ByteMem.write width (evalSymMem state mem) (evalSymExpr state addr) (evalSymExpr state value)
end

@[simp] def evalSymPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) : SymPC Reg → Bool
  | .true => true
  | .eq lhs rhs => evalSymExpr state lhs == evalSymExpr state rhs
  | .lt lhs rhs => decide (evalSymExpr state lhs < evalSymExpr state rhs)
  | .le lhs rhs => decide (evalSymExpr state lhs ≤ evalSymExpr state rhs)
  | .and φ ψ => evalSymPC state φ && evalSymPC state ψ
  | .not φ => !(evalSymPC state φ)


/-! ### Narrowing/extension idempotence lemmas

Since `evalSymExpr` maps both `.low32` and `.uext32` to `mask32`, chains of
these operations are idempotent. These lemmas are used in WitnessSemClosed
proofs to show that `substSymPC` lifting preserves closure membership
despite introducing redundant narrowing chains. -/

@[simp] theorem evalSymExpr_uext32_low32 {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (e : SymExpr Reg) :
    evalSymExpr state (.uext32 (.low32 e)) = evalSymExpr state (.uext32 e) := by
  simp [evalSymExpr, mask32_idempotent]

@[simp] theorem evalSymExpr_low32_uext32 {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (e : SymExpr Reg) :
    evalSymExpr state (.low32 (.uext32 e)) = evalSymExpr state (.low32 e) := by
  simp [evalSymExpr, mask32_idempotent]

@[simp] theorem evalSymExpr_low32_low32 {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (e : SymExpr Reg) :
    evalSymExpr state (.low32 (.low32 e)) = evalSymExpr state (.low32 e) := by
  simp [evalSymExpr, mask32_idempotent]

@[simp] theorem evalSymExpr_uext32_uext32 {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (e : SymExpr Reg) :
    evalSymExpr state (.uext32 (.uext32 e)) = evalSymExpr state (.uext32 e) := by
  simp [evalSymExpr, mask32_idempotent]

def satisfiesSymPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (pc : SymPC Reg) : Prop :=
  evalSymPC state pc = true

mutual
def substSymExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) : SymExpr Reg → SymExpr Reg
  | .const value => .const value
  | .reg reg => sub.regs reg
  | .low32 expr => .low32 (substSymExpr sub expr)
  | .uext32 expr => .uext32 (substSymExpr sub expr)
  | .sext8to32 expr => .sext8to32 (substSymExpr sub expr)
  | .sext32to64 expr => .sext32to64 (substSymExpr sub expr)
  | .sub32 lhs rhs => .sub32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .shl32 lhs rhs => .shl32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .and32 lhs rhs => .and32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .or32 lhs rhs => .or32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .xor32 lhs rhs => .xor32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .add64 lhs rhs => .add64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .sub64 lhs rhs => .sub64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .xor64 lhs rhs => .xor64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .and64 lhs rhs => .and64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .or64 lhs rhs => .or64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .shl64 lhs rhs => .shl64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .shr64 lhs rhs => .shr64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .mul64 lhs rhs => .mul64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .mul32 lhs rhs => .mul32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .not64 x => .not64 (substSymExpr sub x)
  | .not32 x => .not32 (substSymExpr sub x)
  | .sar64 lhs rhs => .sar64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .sar32 lhs rhs => .sar32 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .ite cond t f => .ite (substSymExpr sub cond) (substSymExpr sub t) (substSymExpr sub f)
  | .load width mem addr => .load width (substSymMem sub mem) (substSymExpr sub addr)

def substSymMem {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) : SymMem Reg → SymMem Reg
  | .base => sub.mem
  | .store width mem addr value =>
      .store width (substSymMem sub mem) (substSymExpr sub addr) (substSymExpr sub value)
end


def substSymPC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq lhs rhs => .eq (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .lt lhs rhs => .lt (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .le lhs rhs => .le (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .and φ ψ => .and (substSymPC sub φ) (substSymPC sub ψ)
  | .not φ => .not (substSymPC sub φ)


def composeSymSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) : SymSub Reg :=
  { regs := fun reg => substSymExpr sub₁ (sub₂.regs reg)
  , mem := substSymMem sub₁ sub₂.mem }


def applySymSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (state : ConcreteState Reg) : ConcreteState Reg :=
  { regs := fun reg => evalSymExpr state (sub.regs reg)
  , mem := evalSymMem state sub.mem }

theorem applySymSub_write {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (input : ConcreteState Reg) (reg : Reg) (expr : SymExpr Reg) :
    applySymSub (SymSub.write sub reg expr) input =
      (applySymSub sub input).write reg (evalSymExpr input expr) := by
  apply ConcreteState.ext
  · funext reg'
    by_cases h : reg' = reg
    · subst h
      simp [applySymSub, SymSub.write, ConcreteState.write]
    · simp [applySymSub, SymSub.write, ConcreteState.write, h]
  · rfl

@[simp] theorem ConcreteState.read_applySymSub {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (state : ConcreteState Reg) (reg : Reg) :
    (applySymSub sub state).read reg = evalSymExpr state (sub.regs reg) := by
  rfl


def Summary.id {Reg : Type} : Summary Reg :=
  { sub := SymSub.id
  , pc := .true }


def Summary.apply {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) (state : ConcreteState Reg) : ConcreteState Reg :=
  applySymSub summary.sub state


def Summary.enabled {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (summary : Summary Reg) (state : ConcreteState Reg) : Prop :=
  satisfiesSymPC state summary.pc


def Summary.compose {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Summary Reg) : Summary Reg :=
  { sub := composeSymSub left.sub right.sub
  , pc := .and left.pc (substSymPC left.sub right.pc) }

mutual
theorem substSymExpr_id {Reg : Type} [DecidableEq Reg] [Fintype Reg] (expr : SymExpr Reg) :
    substSymExpr SymSub.id expr = expr := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | low32 expr => simp [substSymExpr, substSymExpr_id]
  | uext32 expr => simp [substSymExpr, substSymExpr_id]
  | sext8to32 expr => simp [substSymExpr, substSymExpr_id]
  | sext32to64 expr => simp [substSymExpr, substSymExpr_id]
  | sub32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | shl32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | and32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | or32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | xor32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | add64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | sub64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | xor64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | and64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | or64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | shl64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | shr64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | mul64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | mul32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | not64 x =>
      simp [substSymExpr, substSymExpr_id]
  | not32 x =>
      simp [substSymExpr, substSymExpr_id]
  | sar64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | sar32 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | ite cond t f =>
      simp [substSymExpr, substSymExpr_id]
  | load width mem addr =>
      simp [substSymExpr, substSymMem_id, substSymExpr_id]

theorem substSymMem_id {Reg : Type} [DecidableEq Reg] [Fintype Reg] (mem : SymMem Reg) :
    substSymMem SymSub.id mem = mem := by
  cases mem with
  | base => rfl
  | store width mem addr value =>
      simp [substSymMem, substSymMem_id, substSymExpr_id]
end

theorem substSymPC_id {Reg : Type} [DecidableEq Reg] [Fintype Reg] (pc : SymPC Reg) :
    substSymPC SymSub.id pc = pc := by
  induction pc with
  | true => rfl
  | eq l r => simp [substSymPC, substSymExpr_id]
  | lt l r => simp [substSymPC, substSymExpr_id]
  | le l r => simp [substSymPC, substSymExpr_id]
  | and φ ψ ihφ ihψ => simp [substSymPC, ihφ, ihψ]
  | not φ ih => simp [substSymPC, ih]

mutual
theorem substSymExpr_compose {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) (expr : SymExpr Reg) :
    substSymExpr (composeSymSub sub₁ sub₂) expr = substSymExpr sub₁ (substSymExpr sub₂ expr) := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | low32 expr => simp [substSymExpr, substSymExpr_compose]
  | uext32 expr => simp [substSymExpr, substSymExpr_compose]
  | sext8to32 expr => simp [substSymExpr, substSymExpr_compose]
  | sext32to64 expr => simp [substSymExpr, substSymExpr_compose]
  | sub32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | shl32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | and32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | or32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | xor32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | add64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | sub64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | xor64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | and64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | or64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | shl64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | shr64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | mul64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | mul32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | not64 x =>
      simp [substSymExpr, substSymExpr_compose]
  | not32 x =>
      simp [substSymExpr, substSymExpr_compose]
  | sar64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | sar32 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | ite cond t f =>
      simp [substSymExpr, substSymExpr_compose]
  | load width mem addr =>
      simp [substSymExpr, substSymMem_compose, substSymExpr_compose]

theorem substSymMem_compose {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) (mem : SymMem Reg) :
    substSymMem (composeSymSub sub₁ sub₂) mem = substSymMem sub₁ (substSymMem sub₂ mem) := by
  cases mem with
  | base => rfl
  | store width mem addr value =>
      simp [substSymMem, substSymMem_compose, substSymExpr_compose]
end

mutual
theorem evalSymExpr_subst {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (expr : SymExpr Reg) (state : ConcreteState Reg) :
    evalSymExpr state (substSymExpr sub expr) = evalSymExpr (applySymSub sub state) expr := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | low32 expr => simp [substSymExpr, evalSymExpr_subst]
  | uext32 expr => simp [substSymExpr, evalSymExpr_subst]
  | sext8to32 expr => simp [substSymExpr, evalSymExpr_subst]
  | sext32to64 expr => simp [substSymExpr, evalSymExpr_subst]
  | sub32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | shl32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | and32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | or32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | xor32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | add64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | sub64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | xor64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | and64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | or64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | shl64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | shr64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | mul64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | mul32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | not64 x =>
      simp [substSymExpr, evalSymExpr_subst]
  | not32 x =>
      simp [substSymExpr, evalSymExpr_subst]
  | sar64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | sar32 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | ite cond t f =>
      simp [substSymExpr, evalSymExpr_subst]
  | load width mem addr =>
      simp [substSymExpr, evalSymMem_subst, evalSymExpr_subst]

theorem evalSymMem_subst {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (mem : SymMem Reg) (state : ConcreteState Reg) :
    evalSymMem state (substSymMem sub mem) = evalSymMem (applySymSub sub state) mem := by
  cases mem with
  | base => rfl
  | store width mem addr value =>
      simp [substSymMem, evalSymMem_subst, evalSymExpr_subst]
end

theorem evalSymPC_subst {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (pc : SymPC Reg) (state : ConcreteState Reg) :
    evalSymPC state (substSymPC sub pc) = evalSymPC (applySymSub sub state) pc := by
  induction pc with
  | true => rfl
  | eq lhs rhs => simp [substSymPC, evalSymExpr_subst]
  | lt lhs rhs => simp [substSymPC, evalSymExpr_subst]
  | le lhs rhs => simp [substSymPC, evalSymExpr_subst]
  | and φ ψ ihφ ihψ => simp [substSymPC, ihφ, ihψ]
  | not φ ih => simp [substSymPC, ih]

@[simp] theorem applySymSub_id {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) :
    applySymSub SymSub.id state = state := by
  apply ConcreteState.ext
  · funext reg
    simp [applySymSub, SymSub.id]
  · simp [applySymSub, SymSub.id, evalSymMem]

@[simp] theorem composeSymSub_apply {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub₁ sub₂ : SymSub Reg) (state : ConcreteState Reg) :
    applySymSub (composeSymSub sub₁ sub₂) state = applySymSub sub₂ (applySymSub sub₁ state) := by
  apply ConcreteState.ext
  · funext reg
    simp [applySymSub, composeSymSub, evalSymExpr_subst]
  · simp [applySymSub, composeSymSub, evalSymMem_subst]

@[simp] theorem Summary.compose_enabled_iff {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Summary Reg) (state : ConcreteState Reg) :
    Summary.enabled (Summary.compose left right) state ↔
      Summary.enabled left state ∧ Summary.enabled right (Summary.apply left state) := by
  simp [Summary.enabled, Summary.compose, Summary.apply, satisfiesSymPC, evalSymPC_subst]

@[simp] theorem Summary.compose_apply {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Summary Reg) (state : ConcreteState Reg) :
    Summary.apply (Summary.compose left right) state =
      Summary.apply right (Summary.apply left state) := by
  simp [Summary.apply, Summary.compose, composeSymSub_apply]

@[simp] theorem Summary.id_enabled {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) :
    Summary.enabled (Summary.id : Summary Reg) state := by
  simp [Summary.id, Summary.enabled, satisfiesSymPC]

@[simp] theorem Summary.id_apply {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) :
    Summary.apply (Summary.id : Summary Reg) state = state := by
  simp [Summary.id, Summary.apply]

/-! ## Hashable instances for fast HashSet-based computation -/

mutual
/-- Depth-limited hash for SymExpr. Recurses at most `d` levels.
    Provides good discrimination from top-level structure while avoiding
    O(tree_depth) traversal of deep expression trees. -/
def hashSymExprD {Reg : Type} [Hashable Reg] (d : Nat) : SymExpr Reg → UInt64
  | .const v => mixHash 1 (hash v)
  | .reg r => mixHash 2 (hash r)
  | _ => if d == 0 then 0 else match ‹SymExpr Reg› with
  | .low32 e => mixHash 3 (hashSymExprD (d-1) e)
  | .uext32 e => mixHash 4 (hashSymExprD (d-1) e)
  | .sext8to32 e => mixHash 5 (hashSymExprD (d-1) e)
  | .sext32to64 e => mixHash 6 (hashSymExprD (d-1) e)
  | .sub32 l r => mixHash 7 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .shl32 l r => mixHash 8 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .and32 l r => mixHash 17 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .or32 l r => mixHash 41 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .xor32 l r => mixHash 41 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .add64 l r => mixHash 9 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .sub64 l r => mixHash 10 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .xor64 l r => mixHash 11 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .and64 l r => mixHash 12 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .or64 l r => mixHash 13 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .shl64 l r => mixHash 14 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .shr64 l r => mixHash 15 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .mul64 l r => mixHash 42 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .mul32 l r => mixHash 43 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .not64 x => mixHash 44 (hashSymExprD (d-1) x)
  | .not32 x => mixHash 45 (hashSymExprD (d-1) x)
  | .sar64 l r => mixHash 46 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .sar32 l r => mixHash 47 (mixHash (hashSymExprD (d-1) l) (hashSymExprD (d-1) r))
  | .ite c t f => mixHash 48 (mixHash (hashSymExprD (d-1) c) (mixHash (hashSymExprD (d-1) t) (hashSymExprD (d-1) f)))
  | .load w m a => mixHash 16 (mixHash (hash w.byteCount) (mixHash (hashSymMemD (d-1) m) (hashSymExprD (d-1) a)))
  | .const _ => 0  -- unreachable, handled above
  | .reg _ => 0    -- unreachable, handled above

/-- Depth-limited hash for SymMem. -/
def hashSymMemD {Reg : Type} [Hashable Reg] (d : Nat) : SymMem Reg → UInt64
  | .base => 17
  | .store w m a v =>
    if d == 0 then 18
    else mixHash 18 (mixHash (hash w.byteCount) (mixHash (hashSymMemD (d-1) m) (mixHash (hashSymExprD (d-1) a) (hashSymExprD (d-1) v))))
end

/-- Default hash depth: 4 levels gives O(~256) nodes max per hash.
    Provides good discrimination while avoiding O(10K+) traversals. -/
def hashSymExpr {Reg : Type} [Hashable Reg] : SymExpr Reg → UInt64 := hashSymExprD 4
def hashSymMem {Reg : Type} [Hashable Reg] : SymMem Reg → UInt64 := hashSymMemD 4

instance {Reg : Type} [Hashable Reg] : Hashable (SymExpr Reg) := ⟨hashSymExpr⟩
instance {Reg : Type} [Hashable Reg] : Hashable (SymMem Reg) := ⟨hashSymMem⟩

def hashSymPC {Reg : Type} [Hashable Reg] : SymPC Reg → UInt64
  | .true => 19
  | .eq l r => mixHash 20 (mixHash (hash l) (hash r))
  | .lt l r => mixHash 21 (mixHash (hash l) (hash r))
  | .le l r => mixHash 22 (mixHash (hash l) (hash r))
  | .and φ ψ => mixHash 23 (mixHash (hashSymPC φ) (hashSymPC ψ))
  | .not φ => mixHash 24 (hashSymPC φ)

instance {Reg : Type} [Hashable Reg] : Hashable (SymPC Reg) := ⟨hashSymPC⟩

instance {Reg : Type} [Hashable Reg] [EnumReg Reg] : Hashable (SymSub Reg) where
  hash sub :=
    -- Register-only hash: skip deep memory chain traversal for performance.
    -- Memory differences still caught by structural equality on hash collision.
    EnumReg.allRegs.foldl (fun acc r => mixHash acc (hash (sub.regs r))) 0

instance {Reg : Type} [Hashable Reg] [EnumReg Reg] : Hashable (Summary Reg) where
  hash s := mixHash (hash s.sub) (hash s.pc)

end VexISA
