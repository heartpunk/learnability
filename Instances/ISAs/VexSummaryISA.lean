import Core.SymbolicISA
import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

private theorem substSymPC_compose (sub₁ sub₂ : SymSub) (pc : SymPC) :
    substSymPC (composeSymSub sub₁ sub₂) pc = substSymPC sub₁ (substSymPC sub₂ pc) := by
  induction pc with
  | true => rfl
  | eq lhs rhs => simp [substSymPC, substSymExpr_compose]
  | and φ ψ ihφ ihψ => simp [substSymPC, ihφ, ihψ]
  | not φ ih => simp [substSymPC, ih]

/-- `SymbolicISA` instance for the current register-only VEX summary algebra. -/
def vexSummaryISA : SymbolicISA SymSub SymPC ConcreteState where
  id_sub := SymSub.id
  compose_sub := composeSymSub
  eval_sub := applySymSub
  pc_true := .true
  pc_and := .and
  pc_lift := substSymPC
  satisfies := satisfiesSymPC
  eval_compose := composeSymSub_apply
  eval_id := applySymSub_id
  compose_id_left := by
    intro sub
    apply SymSub.ext
    · exact substSymExpr_id (sub.regs .rax)
    · exact substSymExpr_id (sub.regs .rcx)
    · exact substSymExpr_id (sub.regs .rdi)
    · exact substSymExpr_id (sub.regs .rip)
    · exact substSymMem_id sub.mem
  compose_id_right := by
    intro sub
    apply SymSub.ext <;> rfl
  compose_assoc := by
    intro sub₁ sub₂ sub₃
    apply SymSub.ext
    · exact (substSymExpr_compose sub₁ sub₂ (sub₃.regs .rax)).symm
    · exact (substSymExpr_compose sub₁ sub₂ (sub₃.regs .rcx)).symm
    · exact (substSymExpr_compose sub₁ sub₂ (sub₃.regs .rdi)).symm
    · exact (substSymExpr_compose sub₁ sub₂ (sub₃.regs .rip)).symm
    · exact (substSymMem_compose sub₁ sub₂ sub₃.mem).symm
  sat_true := by
    intro state
    rfl
  sat_and := by
    intro state φ₁ φ₂
    show evalSymPC state (.and φ₁ φ₂) = true ↔ evalSymPC state φ₁ = true ∧ evalSymPC state φ₂ = true
    simp [evalSymPC]
  sat_lift := by
    intro state sub φ
    show evalSymPC state (substSymPC sub φ) = true ↔ evalSymPC (applySymSub sub state) φ = true
    rw [evalSymPC_subst]
  pc_not := .not
  sat_not := by
    intro state φ
    show evalSymPC state (.not φ) = true ↔ ¬ evalSymPC state φ = true
    cases h : evalSymPC state φ <;> simp [evalSymPC, h]

end VexISA
