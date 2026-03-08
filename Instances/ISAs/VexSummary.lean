import Instances.ISAs.VexISA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

mutual
inductive SymExpr where
  | const : UInt64 → SymExpr
  | reg : Reg → SymExpr
  | add64 : SymExpr → SymExpr → SymExpr
  | load64 : SymMem → SymExpr → SymExpr
  deriving DecidableEq, Repr

inductive SymMem where
  | base
  | store64 : SymMem → SymExpr → SymExpr → SymMem
  deriving DecidableEq, Repr
end

inductive SymPC where
  | true
  | eq : SymExpr → SymExpr → SymPC
  | and : SymPC → SymPC → SymPC
  | not : SymPC → SymPC
  deriving DecidableEq, Repr

structure SymSub where
  regs : Reg → SymExpr
  mem : SymMem

abbrev SymTempEnv := Nat → SymExpr

structure Summary where
  sub : SymSub
  pc : SymPC

@[ext] theorem SymSub.ext {sub₁ sub₂ : SymSub}
    (hRax : sub₁.regs .rax = sub₂.regs .rax)
    (hRcx : sub₁.regs .rcx = sub₂.regs .rcx)
    (hRdi : sub₁.regs .rdi = sub₂.regs .rdi)
    (hRip : sub₁.regs .rip = sub₂.regs .rip)
    (hMem : sub₁.mem = sub₂.mem) :
    sub₁ = sub₂ := by
  cases sub₁
  cases sub₂
  simp at hRax hRcx hRdi hRip hMem
  refine ?_
  congr
  funext reg
  cases reg with
  | rax => exact hRax
  | rcx => exact hRcx
  | rdi => exact hRdi
  | rip => exact hRip

instance : DecidableEq SymSub := by
  intro sub₁ sub₂
  by_cases hRax : sub₁.regs .rax = sub₂.regs .rax
  · by_cases hRcx : sub₁.regs .rcx = sub₂.regs .rcx
    · by_cases hRdi : sub₁.regs .rdi = sub₂.regs .rdi
      · by_cases hRip : sub₁.regs .rip = sub₂.regs .rip
        · by_cases hMem : sub₁.mem = sub₂.mem
          · exact isTrue (SymSub.ext hRax hRcx hRdi hRip hMem)
          · exact isFalse (fun h => hMem (congrArg SymSub.mem h))
        · exact isFalse (fun h => hRip (congrArg (fun sub => sub.regs .rip) h))
      · exact isFalse (fun h => hRdi (congrArg (fun sub => sub.regs .rdi) h))
    · exact isFalse (fun h => hRcx (congrArg (fun sub => sub.regs .rcx) h))
  · exact isFalse (fun h => hRax (congrArg (fun sub => sub.regs .rax) h))

instance : DecidableEq Summary := by
  intro left right
  by_cases hSub : left.sub = right.sub
  · by_cases hPc : left.pc = right.pc
    · exact isTrue (by cases left; cases right; cases hSub; cases hPc; rfl)
    · exact isFalse (fun h => hPc (by cases h; rfl))
  · exact isFalse (fun h => hSub (by cases h; rfl))


def SymSub.id : SymSub :=
  { regs := SymExpr.reg
  , mem := .base }


def SymSub.write (sub : SymSub) (reg : Reg) (expr : SymExpr) : SymSub :=
  { sub with regs := fun reg' => if reg' = reg then expr else sub.regs reg' }


def SymSub.writeMem (sub : SymSub) (mem : SymMem) : SymSub :=
  { sub with mem := mem }

@[simp] theorem SymSub.write_same (sub : SymSub) (reg : Reg) (expr : SymExpr) :
    (SymSub.write sub reg expr).regs reg = expr := by
  simp [SymSub.write]

@[simp] theorem SymSub.write_other (sub : SymSub) {reg reg' : Reg} (expr : SymExpr)
    (h : reg' ≠ reg) : (SymSub.write sub reg expr).regs reg' = sub.regs reg' := by
  simp [SymSub.write, h]


def SymTempEnv.empty : SymTempEnv := fun _ => .const 0

def SymTempEnv.write (temps : SymTempEnv) (tmp : Nat) (expr : SymExpr) : SymTempEnv :=
  fun tmp' => if tmp' = tmp then expr else temps tmp'

@[simp] theorem SymTempEnv.write_same (temps : SymTempEnv) (tmp : Nat) (expr : SymExpr) :
    SymTempEnv.write temps tmp expr tmp = expr := by
  simp [SymTempEnv.write]

@[simp] theorem SymTempEnv.write_other (temps : SymTempEnv) {tmp tmp' : Nat} (expr : SymExpr)
    (h : tmp' ≠ tmp) : SymTempEnv.write temps tmp expr tmp' = temps tmp' := by
  simp [SymTempEnv.write, h]

mutual
@[simp] def evalSymExpr (state : ConcreteState) : SymExpr → UInt64
  | .const value => value
  | .reg reg => state.read reg
  | .add64 lhs rhs => evalSymExpr state lhs + evalSymExpr state rhs
  | .load64 mem addr => ByteMem.read64le (evalSymMem state mem) (evalSymExpr state addr)

@[simp] def evalSymMem (state : ConcreteState) : SymMem → ByteMem
  | .base => state.mem
  | .store64 mem addr value =>
      ByteMem.write64le (evalSymMem state mem) (evalSymExpr state addr) (evalSymExpr state value)
end

@[simp] def evalSymPC (state : ConcreteState) : SymPC → Bool
  | .true => true
  | .eq lhs rhs => evalSymExpr state lhs == evalSymExpr state rhs
  | .and φ ψ => evalSymPC state φ && evalSymPC state ψ
  | .not φ => !(evalSymPC state φ)


def satisfiesSymPC (state : ConcreteState) (pc : SymPC) : Prop :=
  evalSymPC state pc = true

mutual
def substSymExpr (sub : SymSub) : SymExpr → SymExpr
  | .const value => .const value
  | .reg reg => sub.regs reg
  | .add64 lhs rhs => .add64 (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .load64 mem addr => .load64 (substSymMem sub mem) (substSymExpr sub addr)

def substSymMem (sub : SymSub) : SymMem → SymMem
  | .base => sub.mem
  | .store64 mem addr value => .store64 (substSymMem sub mem) (substSymExpr sub addr) (substSymExpr sub value)
end


def substSymPC (sub : SymSub) : SymPC → SymPC
  | .true => .true
  | .eq lhs rhs => .eq (substSymExpr sub lhs) (substSymExpr sub rhs)
  | .and φ ψ => .and (substSymPC sub φ) (substSymPC sub ψ)
  | .not φ => .not (substSymPC sub φ)


def composeSymSub (sub₁ sub₂ : SymSub) : SymSub :=
  { regs := fun reg => substSymExpr sub₁ (sub₂.regs reg)
  , mem := substSymMem sub₁ sub₂.mem }


def applySymSub (sub : SymSub) (state : ConcreteState) : ConcreteState :=
  { rax := evalSymExpr state (sub.regs .rax)
  , rcx := evalSymExpr state (sub.regs .rcx)
  , rdi := evalSymExpr state (sub.regs .rdi)
  , rip := evalSymExpr state (sub.regs .rip)
  , mem := evalSymMem state sub.mem }

@[simp] theorem ConcreteState.read_applySymSub (sub : SymSub) (state : ConcreteState) (reg : Reg) :
    (applySymSub sub state).read reg = evalSymExpr state (sub.regs reg) := by
  cases reg <;> rfl


def Summary.id : Summary :=
  { sub := SymSub.id, pc := .true }


def Summary.apply (summary : Summary) (state : ConcreteState) : ConcreteState :=
  applySymSub summary.sub state


def Summary.enabled (summary : Summary) (state : ConcreteState) : Prop :=
  satisfiesSymPC state summary.pc


def Summary.compose (left right : Summary) : Summary :=
  { sub := composeSymSub left.sub right.sub
  , pc := .and left.pc (substSymPC left.sub right.pc) }

mutual
theorem substSymExpr_id (expr : SymExpr) :
    substSymExpr SymSub.id expr = expr := by
  cases expr with
  | const value => rfl
  | reg reg => cases reg <;> rfl
  | add64 lhs rhs =>
      simp [substSymExpr, substSymExpr_id]
  | load64 mem addr =>
      simp [substSymExpr, substSymMem_id, substSymExpr_id]

theorem substSymMem_id (mem : SymMem) :
    substSymMem SymSub.id mem = mem := by
  cases mem with
  | base => rfl
  | store64 mem addr value =>
      simp [substSymMem, substSymMem_id, substSymExpr_id]
end

mutual
theorem substSymExpr_compose (sub₁ sub₂ : SymSub) (expr : SymExpr) :
    substSymExpr (composeSymSub sub₁ sub₂) expr = substSymExpr sub₁ (substSymExpr sub₂ expr) := by
  cases expr with
  | const value => rfl
  | reg reg => rfl
  | add64 lhs rhs =>
      simp [substSymExpr, substSymExpr_compose]
  | load64 mem addr =>
      simp [substSymExpr, substSymMem_compose, substSymExpr_compose]

theorem substSymMem_compose (sub₁ sub₂ : SymSub) (mem : SymMem) :
    substSymMem (composeSymSub sub₁ sub₂) mem = substSymMem sub₁ (substSymMem sub₂ mem) := by
  cases mem with
  | base => rfl
  | store64 mem addr value =>
      simp [substSymMem, substSymMem_compose, substSymExpr_compose]
end

mutual
theorem evalSymExpr_subst (sub : SymSub) (expr : SymExpr) (state : ConcreteState) :
    evalSymExpr state (substSymExpr sub expr) = evalSymExpr (applySymSub sub state) expr := by
  cases expr with
  | const value => rfl
  | reg reg => cases reg <;> rfl
  | add64 lhs rhs =>
      simp [substSymExpr, evalSymExpr_subst]
  | load64 mem addr =>
      simp [substSymExpr, evalSymMem_subst, evalSymExpr_subst]

theorem evalSymMem_subst (sub : SymSub) (mem : SymMem) (state : ConcreteState) :
    evalSymMem state (substSymMem sub mem) = evalSymMem (applySymSub sub state) mem := by
  cases mem with
  | base => rfl
  | store64 mem addr value =>
      simp [substSymMem, evalSymMem_subst, evalSymExpr_subst]
end

theorem evalSymPC_subst (sub : SymSub) (pc : SymPC) (state : ConcreteState) :
    evalSymPC state (substSymPC sub pc) = evalSymPC (applySymSub sub state) pc := by
  induction pc with
  | true => rfl
  | eq lhs rhs => simp [substSymPC, evalSymExpr_subst]
  | and φ ψ ihφ ihψ => simp [substSymPC, ihφ, ihψ]
  | not φ ih => simp [substSymPC, ih]

@[simp] theorem applySymSub_id (state : ConcreteState) :
    applySymSub SymSub.id state = state := by
  cases state with
  | mk rax rcx rdi rip mem =>
      simp [applySymSub, SymSub.id, evalSymMem]

@[simp] theorem composeSymSub_apply (sub₁ sub₂ : SymSub) (state : ConcreteState) :
    applySymSub (composeSymSub sub₁ sub₂) state = applySymSub sub₂ (applySymSub sub₁ state) := by
  cases state with
  | mk rax rcx rdi rip mem =>
      simp [applySymSub, composeSymSub, evalSymExpr_subst, evalSymMem_subst]

end VexISA
