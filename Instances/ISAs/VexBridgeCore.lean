import Mathlib.Data.Fintype.Basic
import Instances.ISAs.VexConcrete
import Instances.ISAs.VexLowerCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

private theorem beq_false_of_ne {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : a ≠ b) :
    (a == b) = false := by
  cases hEq : (a == b) with
  | false => rfl
  | true =>
      exfalso
      exact h (beq_iff_eq.mp hEq)

private theorem eval_lowerAmd64CalculateConditionZero {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (ccOp ccDep1 ccDep2 : SymExpr Reg) :
    evalSymPC state (lowerAmd64CalculateConditionZero ccOp ccDep1 ccDep2) =
      evalAmd64CalculateConditionZero
        (evalSymExpr state ccOp)
        (evalSymExpr state ccDep1)
        (evalSymExpr state ccDep2)
        0 := by
  by_cases h3 : evalSymExpr state ccOp = 0x3
  · simp [lowerAmd64CalculateConditionZero, pcOr, evalAmd64CalculateConditionZero, h3, mask32]
  · by_cases h7 : evalSymExpr state ccOp = 0x7
    · have hEq3 : (evalSymExpr state ccOp == 0x3) = false := beq_false_of_ne h3
      simp [lowerAmd64CalculateConditionZero, pcOr, evalAmd64CalculateConditionZero, h7, mask32]
    · by_cases h13 : evalSymExpr state ccOp = 0x13
      · have hEq3 : (evalSymExpr state ccOp == 0x3) = false := beq_false_of_ne h3
        have hEq7 : (evalSymExpr state ccOp == 0x7) = false := beq_false_of_ne h7
        simp [lowerAmd64CalculateConditionZero, pcOr, evalAmd64CalculateConditionZero, h13, mask32]
      · have hEq3 : (evalSymExpr state ccOp == 0x3) = false := beq_false_of_ne h3
        have hEq7 : (evalSymExpr state ccOp == 0x7) = false := beq_false_of_ne h7
        have hEq13 : (evalSymExpr state ccOp == 0x13) = false := beq_false_of_ne h13
        simp [lowerAmd64CalculateConditionZero, pcOr, evalAmd64CalculateConditionZero, h3, h7, h13, hEq3, hEq7, hEq13, mask32]

private theorem beq_zero_eq_not_bne_zero (a : UInt64) : (a == 0) = !(a != 0) := by
  show (a == 0) = !!(a == 0)
  simp [Bool.not_not]

private theorem eval_lowerAmd64CalculateConditionSign {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (ccOp ccDep1 ccDep2 : SymExpr Reg) :
    evalSymPC state (lowerAmd64CalculateConditionSign ccOp ccDep1 ccDep2) =
      evalAmd64CalculateConditionSign
        (evalSymExpr state ccOp)
        (evalSymExpr state ccDep1)
        (evalSymExpr state ccDep2)
        0 := by
  by_cases h7 : evalSymExpr state ccOp = 0x7
  · simp [lowerAmd64CalculateConditionSign, pcOr, evalAmd64CalculateConditionSign, h7, mask32,
      beq_zero_eq_not_bne_zero]
  · by_cases h3 : evalSymExpr state ccOp = 0x3
    · have hEq7 := beq_false_of_ne h7
      simp [lowerAmd64CalculateConditionSign, pcOr, evalAmd64CalculateConditionSign, h3, mask32,
        beq_zero_eq_not_bne_zero]
    · by_cases h13 : evalSymExpr state ccOp = 0x13
      · have hEq7 := beq_false_of_ne h7; have hEq3 := beq_false_of_ne h3
        simp [lowerAmd64CalculateConditionSign, pcOr, evalAmd64CalculateConditionSign, h13, mask32,
          beq_zero_eq_not_bne_zero]
      · have hEq7 := beq_false_of_ne h7; have hEq3 := beq_false_of_ne h3
        have hEq13 := beq_false_of_ne h13
        simp [lowerAmd64CalculateConditionSign, pcOr, evalAmd64CalculateConditionSign,
          h7, h3, h13, hEq7, hEq3, hEq13, mask32]

private theorem parity8_mask32 (x : UInt64) : parity8 (mask32 x) = parity8 x := by
  simp only [parity8, mask32]; bv_decide

private theorem parity8_sub_mask32 (a b : UInt64) :
    parity8 (a - b) = parity8 (mask32 a - mask32 b) := by
  simp only [parity8, mask32]; bv_decide

private theorem parity8_add_mask32 (a b : UInt64) :
    parity8 (a + b) = parity8 (mask32 a + mask32 b) := by
  simp only [parity8, mask32]; bv_decide

private theorem eval_symParity8 {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (result : SymExpr Reg) :
    evalSymPC state (symParity8 result) = parity8 (evalSymExpr state result) := by
  simp only [symParity8, parity8, evalSymPC, evalSymExpr, shiftRight64, maskShift64]
  have h4 : (4 : UInt64) &&& 63 = 4 := by native_decide
  have h2 : (2 : UInt64) &&& 63 = 2 := by native_decide
  have h1 : (1 : UInt64) &&& 63 = 1 := by native_decide
  rw [h4, h2, h1]
  -- .shiftRight and >>> are definitionally equal
  rfl

private theorem eval_lowerAmd64CalculateConditionP {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (ccOp ccDep1 ccDep2 : SymExpr Reg) :
    evalSymPC state (lowerAmd64CalculateConditionP ccOp ccDep1 ccDep2) =
      evalAmd64CalculateConditionP
        (evalSymExpr state ccOp)
        (evalSymExpr state ccDep1)
        (evalSymExpr state ccDep2)
        0 := by
  by_cases h7 : evalSymExpr state ccOp = 0x7
  · simp [lowerAmd64CalculateConditionP, pcOr, evalAmd64CalculateConditionP, evalSymPC,
      evalSymExpr, h7, eval_symParity8]
    rw [parity8_mask32, parity8_sub_mask32]
  · by_cases h3 : evalSymExpr state ccOp = 0x3
    · simp [lowerAmd64CalculateConditionP, pcOr, evalAmd64CalculateConditionP, evalSymPC,
        evalSymExpr, h3, beq_false_of_ne h7, eval_symParity8]
      rw [parity8_mask32, parity8_add_mask32]
    · by_cases h13 : evalSymExpr state ccOp = 0x13
      · simp [lowerAmd64CalculateConditionP, pcOr, evalAmd64CalculateConditionP, evalSymPC,
          evalSymExpr, h13, mask32, mask32_idempotent, beq_false_of_ne h7, beq_false_of_ne h3, eval_symParity8]
      · simp [lowerAmd64CalculateConditionP, pcOr, evalAmd64CalculateConditionP, evalSymPC,
          evalSymExpr, h7, h3, h13, beq_false_of_ne h7, beq_false_of_ne h3, beq_false_of_ne h13, mask32]

private theorem eval_lowerAmd64CalculateConditionL {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (ccOp ccDep1 ccDep2 : SymExpr Reg) :
    evalSymPC state (lowerAmd64CalculateConditionL ccOp ccDep1 ccDep2) =
      evalAmd64CalculateConditionL
        (evalSymExpr state ccOp)
        (evalSymExpr state ccDep1)
        (evalSymExpr state ccDep2)
        0 := by
  by_cases h7 : evalSymExpr state ccOp = 0x7
  · simp [lowerAmd64CalculateConditionL, evalAmd64CalculateConditionL, h7]
  · simp [lowerAmd64CalculateConditionL, evalAmd64CalculateConditionL, h7, beq_false_of_ne h7]

private theorem eval_lowerAmd64CalculateConditionB {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (ccOp ccDep1 ccDep2 : SymExpr Reg) :
    evalSymPC state (lowerAmd64CalculateConditionB ccOp ccDep1 ccDep2) =
      evalAmd64CalculateConditionB
        (evalSymExpr state ccOp)
        (evalSymExpr state ccDep1)
        (evalSymExpr state ccDep2)
        0 := by
  by_cases h7 : evalSymExpr state ccOp = 0x7
  · simp [lowerAmd64CalculateConditionB, evalAmd64CalculateConditionB, h7, mask32]
  · have hEq7 := beq_false_of_ne h7
    simp [lowerAmd64CalculateConditionB, evalAmd64CalculateConditionB, h7, hEq7]

private theorem eval_lowerAmd64CalculateConditionLE {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (ccOp ccDep1 ccDep2 : SymExpr Reg) :
    evalSymPC state (lowerAmd64CalculateConditionLE ccOp ccDep1 ccDep2) =
      evalAmd64CalculateConditionLE
        (evalSymExpr state ccOp)
        (evalSymExpr state ccDep1)
        (evalSymExpr state ccDep2)
        0 := by
  by_cases h7 : evalSymExpr state ccOp = 0x7
  · simp [lowerAmd64CalculateConditionLE, evalAmd64CalculateConditionLE, h7]
  · have hEq7 := beq_false_of_ne h7
    simp [lowerAmd64CalculateConditionLE, evalAmd64CalculateConditionLE, h7, hEq7]

/-- Public bridge invariant relating a concrete threaded state to symbolic substitutions and temps. -/
def BridgeInvariant {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg)
    (concrete : ConcreteState Reg × TempEnv) (sub : SymSub Reg) (temps : SymTempEnv Reg) : Prop :=
  concrete.1 = applySymSub sub input ∧
    ∀ tmp, concrete.2 tmp = evalSymExpr input (temps.get tmp)

abbrev LowerStateMatches {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg)
    (concrete : ConcreteState Reg × TempEnv) (symbolic : LowerState Reg) : Prop :=
  BridgeInvariant input concrete symbolic.1 symbolic.2

abbrev PartialSummaryMatches {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg)
    (concrete : ConcreteState Reg × TempEnv) (ps : PartialSummary Reg) : Prop :=
  BridgeInvariant input concrete ps.sub ps.temps

structure LinearStmtBridgeCase {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (stmt : LinearStmt Reg) where
  exec : ConcreteState Reg × TempEnv → ConcreteState Reg × TempEnv
  lower : LowerState Reg → LowerState Reg
  sound :
    ∀ input concrete symbolic,
      LowerStateMatches input concrete symbolic →
      LowerStateMatches input (exec concrete) (lower symbolic)

structure BranchStmtBridgeCase {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (stmt : BranchStmt Reg) where
  fires : ConcreteState Reg × TempEnv → Bool
  taken : ConcreteState Reg × TempEnv → ConcreteState Reg
  cont : ConcreteState Reg × TempEnv → ConcreteState Reg × TempEnv
  lowerGuard : PartialSummary Reg → SymPC Reg
  lowerTaken : PartialSummary Reg → Summary Reg
  lowerContinue : PartialSummary Reg → PartialSummary Reg
  fires_iff_guard :
    ∀ input concrete ps,
      PartialSummaryMatches input concrete ps →
      fires concrete = evalSymPC input (lowerGuard ps)
  taken_sound :
    ∀ input concrete ps,
      PartialSummaryMatches input concrete ps →
      fires concrete = true →
      Summary.apply (lowerTaken ps) input = taken concrete
  continue_matches :
    ∀ input concrete ps,
      PartialSummaryMatches input concrete ps →
      PartialSummaryMatches input (cont concrete) (lowerContinue ps)
  taken_pc_iff :
    ∀ ps input,
      Summary.enabled (lowerTaken ps) input ↔
        (Summary.enabled { sub := ps.sub, pc := ps.pc } input ∧
          evalSymPC input (lowerGuard ps) = true)
  continue_pc_iff :
    ∀ ps input,
      Summary.enabled { sub := (lowerContinue ps).sub, pc := (lowerContinue ps).pc } input ↔
        (Summary.enabled { sub := ps.sub, pc := ps.pc } input ∧
          evalSymPC input (lowerGuard ps) = false)

private theorem lowerExpr_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input state : ConcreteState Reg) (temps : TempEnv) (sub : SymSub Reg) (symTemps : SymTempEnv Reg)
    (hState : state = applySymSub sub input)
    (hTemps : ∀ tmp, temps tmp = evalSymExpr input (symTemps.get tmp))
    (expr : Expr Reg) :
    evalExpr state temps expr = evalSymExpr input (lowerExpr sub symTemps expr) := by
  induction expr with
  | const value => rfl
  | get reg =>
      rw [hState]
      simpa [lowerExpr] using ConcreteState.read_applySymSub sub input reg
  | tmp tmp => simp [lowerExpr, SymTempEnv.get, hTemps]
  | narrow32 expr ih =>
      simp only [evalExpr, lowerExpr, foldUn]; split <;> simp_all [evalSymExpr, mask32]
  | zext64 expr ih =>
      simp only [evalExpr, lowerExpr, foldUn]; split <;> simp_all [evalSymExpr, mask32]
  | sext8to32 expr ih => simp [evalExpr, lowerExpr, ih, signExtend8to32]
  | sext32to64 expr ih => simp [evalExpr, lowerExpr, ih, signExtend32to64]
  | add32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr]; split <;> simp_all [evalSymExpr, mask32]
  | sub32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr, foldBin32]; split <;> simp_all [evalSymExpr, mask32]
  | shl32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr, foldBin32]; split <;> simp_all [evalSymExpr, shiftLeft32]
  | and32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr, foldBin32]; split <;> simp_all [evalSymExpr, mask32]
  | or32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr, foldBin32]; split <;> simp_all [evalSymExpr, mask32]
  | xor32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr, foldBin32]; split <;> simp_all [evalSymExpr, mask32]
  | add64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | sub64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | xor64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | and64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | or64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | shl64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | shr64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | mul64 lhs rhs ihL ihR =>
      simp only [lowerExpr, foldBin64]; split <;> simp_all [evalSymExpr]
  | mul32 lhs rhs ihL ihR =>
      simp only [evalExpr, lowerExpr, foldBin32]; split <;> simp_all [evalSymExpr, mask32]
  | not64 x ih =>
      simp only [evalExpr, lowerExpr, foldUn]; split <;> simp_all [evalSymExpr]
  | not32 x ih =>
      simp only [evalExpr, lowerExpr, foldUn]; split <;> simp_all [evalSymExpr, mask32]
  | sar64 lhs rhs ihL ihR =>
      simp [evalExpr, lowerExpr, ihL, ihR, signedShiftRight64]
  | sar32 lhs rhs ihL ihR =>
      simp [evalExpr, lowerExpr, ihL, ihR, signedShiftRight32]
  | ite cond t f ihC ihT ihF =>
      simp [evalExpr, lowerExpr, ihC, ihT, ihF]
  | load width addr ih =>
      subst state
      simpa [evalExpr, lowerExpr] using
        congrArg (fun value => ByteMem.read width (applySymSub sub input).mem value) ih

private theorem lowerCond_sound {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input state : ConcreteState Reg) (temps : TempEnv) (sub : SymSub Reg) (symTemps : SymTempEnv Reg)
    (hState : state = applySymSub sub input)
    (hTemps : ∀ tmp, temps tmp = evalSymExpr input (symTemps.get tmp))
    (cond : Cond Reg) :
    evalCond state temps cond = evalSymPC input (lowerCond sub symTemps cond) := by
  cases cond with
  | eq64 lhs rhs =>
      simp [lowerCond,
        lowerExpr_sound input state temps sub symTemps hState hTemps lhs,
        lowerExpr_sound input state temps sub symTemps hState hTemps rhs]
  | lt64 lhs rhs =>
      simp [lowerCond,
        lowerExpr_sound input state temps sub symTemps hState hTemps lhs,
        lowerExpr_sound input state temps sub symTemps hState hTemps rhs]
  | le64 lhs rhs =>
      simp [lowerCond,
        lowerExpr_sound input state temps sub symTemps hState hTemps lhs,
        lowerExpr_sound input state temps sub symTemps hState hTemps rhs]
  | ne64 lhs rhs =>
      simp [lowerCond, evalCond, evalSymPC,
        lowerExpr_sound input state temps sub symTemps hState hTemps lhs,
        lowerExpr_sound input state temps sub symTemps hState hTemps rhs]
  | amd64CalculateCondition code ccOp ccDep1 ccDep2 ccNdep =>
      subst state
      have hCcOp :=
        lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps ccOp
      have hCcDep1 :=
        lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps ccDep1
      have hCcDep2 :=
        lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps ccDep2
      have hCcNdep :=
        lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps ccNdep
      by_cases hCode4 : code = 0x4
      · subst hCode4
        simp [evalCond, lowerCond, hCcOp, hCcDep1, hCcDep2,
          eval_lowerAmd64CalculateConditionZero, evalAmd64CalculateConditionZero]
      · by_cases hCode8 : code = 0x8
        · subst hCode8
          simp [evalCond, lowerCond, hCode4, hCcOp, hCcDep1, hCcDep2,
            eval_lowerAmd64CalculateConditionSign, evalAmd64CalculateConditionSign]
        · by_cases hCode9 : code = 0x9
          · subst hCode9
            simp [evalCond, lowerCond, hCode4, hCode8, hCcOp, hCcDep1, hCcDep2,
              eval_lowerAmd64CalculateConditionSign, evalAmd64CalculateConditionSign]
          · by_cases hCodeA : code = 0xA
            · subst hCodeA
              simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCcOp, hCcDep1, hCcDep2,
                eval_lowerAmd64CalculateConditionP, evalAmd64CalculateConditionP]
            · by_cases hCodeB : code = 0xB
              · subst hCodeB
                simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCcOp, hCcDep1, hCcDep2,
                  eval_lowerAmd64CalculateConditionP, evalAmd64CalculateConditionP]
              · by_cases hCode2 : code = 0x2
                · subst hCode2
                  simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCcOp, hCcDep1, hCcDep2,
                    eval_lowerAmd64CalculateConditionB, evalAmd64CalculateConditionB]
                · by_cases hCode3 : code = 0x3
                  · subst hCode3
                    simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCode2, hCcOp, hCcDep1, hCcDep2,
                      eval_lowerAmd64CalculateConditionB, evalAmd64CalculateConditionB]
                  · by_cases hCodeC : code = 0xC
                    · subst hCodeC
                      simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCode2, hCode3, hCcOp, hCcDep1, hCcDep2,
                        eval_lowerAmd64CalculateConditionL, evalAmd64CalculateConditionL]
                    · by_cases hCodeD : code = 0xD
                      · subst hCodeD
                        simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCode2, hCode3, hCodeC, hCcOp, hCcDep1, hCcDep2,
                          eval_lowerAmd64CalculateConditionL, evalAmd64CalculateConditionL]
                      · by_cases hCodeE : code = 0xE
                        · subst hCodeE
                          simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCode2, hCode3, hCodeC, hCodeD,
                            hCcOp, hCcDep1, hCcDep2, eval_lowerAmd64CalculateConditionLE, evalAmd64CalculateConditionLE]
                        · by_cases hCodeF : code = 0xF
                          · subst hCodeF
                            simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCode2, hCode3, hCodeC, hCodeD, hCodeE,
                              hCcOp, hCcDep1, hCcDep2, eval_lowerAmd64CalculateConditionLE, evalAmd64CalculateConditionLE]
                          · simp [evalCond, lowerCond, hCode4, hCode8, hCode9, hCodeA, hCodeB, hCode2, hCode3, hCodeC, hCodeD, hCodeE, hCodeF]

private theorem applySymSub_writeMem {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (sub : SymSub Reg) (input : ConcreteState Reg) (mem : SymMem Reg) :
    applySymSub (SymSub.writeMem sub mem) input =
      { applySymSub sub input with mem := evalSymMem input mem } := by
  apply ConcreteState.ext
  · funext reg
    rfl
  · rfl

@[inline] def linearStmtBridge {Reg : Type} [DecidableEq Reg] [Fintype Reg] :
    (stmt : LinearStmt Reg) → LinearStmtBridgeCase stmt
  | .wrTmp tmp expr =>
      { exec := fun cfg =>
          match cfg with
          | (state, temps) => (state, temps.write tmp (evalExpr state temps expr))
        lower := fun symbolic =>
          match symbolic with
          | (sub, temps) => (sub, SymTempEnv.write temps tmp (lowerExpr sub temps expr))
        sound := by
          intro input concrete symbolic hMatch
          rcases concrete with ⟨state, temps⟩
          rcases symbolic with ⟨sub, symTemps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          constructor
          · simpa using hState
          · intro tmp'
            by_cases h : tmp' = tmp
            · subst h
              have hExpr := lowerExpr_sound input state temps sub symTemps hState hTemps expr
              simp [TempEnv.write, hExpr]
            · simp [TempEnv.write, h, SymTempEnv.get_write_other _ _ h]
              exact hTemps tmp' }
  | .put reg expr =>
      { exec := fun cfg =>
          match cfg with
          | (state, temps) => (state.write reg (evalExpr state temps expr), temps)
        lower := fun symbolic =>
          match symbolic with
          | (sub, temps) => (SymSub.write sub reg (lowerExpr sub temps expr), temps)
        sound := by
          intro input concrete symbolic hMatch
          rcases concrete with ⟨state, temps⟩
          rcases symbolic with ⟨sub, symTemps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          constructor
          · subst hState
            have hExpr := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps expr
            calc
              (applySymSub sub input).write reg (evalExpr (applySymSub sub input) temps expr)
                  = (applySymSub sub input).write reg (evalSymExpr input (lowerExpr sub symTemps expr)) := by
                      simp [hExpr]
              _ = applySymSub (SymSub.write sub reg (lowerExpr sub symTemps expr)) input := by
                      symm
                      simpa using applySymSub_write sub input reg (lowerExpr sub symTemps expr)
          · intro tmp
            simpa using hTemps tmp }
  | .store width addr value =>
      { exec := fun cfg =>
          match cfg with
          | (state, temps) =>
              ({ state with mem := ByteMem.write width state.mem (evalExpr state temps addr) (evalExpr state temps value) }, temps)
        lower := fun symbolic =>
          match symbolic with
          | (sub, temps) =>
              let mem := SymMem.store width sub.mem (lowerExpr sub temps addr) (lowerExpr sub temps value)
              (SymSub.writeMem sub mem, temps)
        sound := by
          intro input concrete symbolic hMatch
          rcases concrete with ⟨state, temps⟩
          rcases symbolic with ⟨sub, symTemps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          constructor
          · subst hState
            have hAddr := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps addr
            have hValue := lowerExpr_sound input (applySymSub sub input) temps sub symTemps rfl hTemps value
            calc
              { applySymSub sub input with
                  mem := ByteMem.write width (applySymSub sub input).mem
                    (evalExpr (applySymSub sub input) temps addr)
                    (evalExpr (applySymSub sub input) temps value) }
                  = { applySymSub sub input with
                        mem := evalSymMem input (SymMem.store width sub.mem (lowerExpr sub symTemps addr) (lowerExpr sub symTemps value)) } := by
                      rw [hAddr, hValue]
                      rfl
              _ = applySymSub (SymSub.writeMem sub (SymMem.store width sub.mem (lowerExpr sub symTemps addr) (lowerExpr sub symTemps value))) input := by
                      symm
                      simpa using applySymSub_writeMem sub input
                        (SymMem.store width sub.mem (lowerExpr sub symTemps addr) (lowerExpr sub symTemps value))
          · intro tmp
            simpa using hTemps tmp }

@[inline] def execLinearStmt {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (cfg : ConcreteState Reg × TempEnv) (stmt : LinearStmt Reg) : ConcreteState Reg × TempEnv :=
  (linearStmtBridge stmt).exec cfg

@[inline] def lowerLinearStmt {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : LowerState Reg) (stmt : LinearStmt Reg) : LowerState Reg :=
  (linearStmtBridge stmt).lower state

@[inline] def branchStmtBridge {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) : (stmt : BranchStmt Reg) → BranchStmtBridgeCase ip_reg stmt
  | .exit cond target =>
      { fires := fun concrete => evalCond concrete.1 concrete.2 cond
        taken := fun concrete => concrete.1.write ip_reg target
        cont := fun concrete => concrete
        lowerGuard := fun ps => lowerCond ps.sub ps.temps cond
        lowerTaken := fun ps =>
          { sub := SymSub.write ps.sub ip_reg (.const target)
          , pc := .and ps.pc (lowerCond ps.sub ps.temps cond) }
        lowerContinue := fun ps =>
          { ps with pc := .and ps.pc (.not (lowerCond ps.sub ps.temps cond)) }
        fires_iff_guard := by
          intro input concrete ps hMatch
          rcases concrete with ⟨state, temps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          simpa using lowerCond_sound input state temps ps.sub ps.temps hState hTemps cond
        taken_sound := by
          intro input concrete ps hMatch hFires
          rcases concrete with ⟨state, temps⟩
          rcases hMatch with ⟨hState, hTemps⟩
          have hApply :
              Summary.apply { sub := SymSub.write ps.sub ip_reg (.const target),
                              pc := .and ps.pc (lowerCond ps.sub ps.temps cond) } input =
                state.write ip_reg target := by
            calc
              Summary.apply { sub := SymSub.write ps.sub ip_reg (.const target),
                              pc := .and ps.pc (lowerCond ps.sub ps.temps cond) } input
                  = (applySymSub ps.sub input).write ip_reg target := by
                      simpa [Summary.apply] using
                        (applySymSub_write ps.sub input ip_reg (.const target))
              _ = state.write ip_reg target := by
                    exact congrArg (fun st => st.write ip_reg target) hState.symm
          change Summary.apply { sub := SymSub.write ps.sub ip_reg (.const target),
                                 pc := .and ps.pc (lowerCond ps.sub ps.temps cond) } input =
            state.write ip_reg target
          exact hApply
        continue_matches := by
          intro input concrete ps hMatch
          simpa [PartialSummaryMatches, BridgeInvariant]
        taken_pc_iff := by
          intro ps input
          constructor
          · intro hEnabled
            rw [Summary.enabled, satisfiesSymPC, evalSymPC] at hEnabled
            have hBoth : evalSymPC input ps.pc = true ∧
                evalSymPC input (lowerCond ps.sub ps.temps cond) = true := by
              simpa [Bool.and_eq_true] using hEnabled
            exact ⟨by simpa [Summary.enabled, satisfiesSymPC] using hBoth.1, hBoth.2⟩
          · intro h
            rcases h with ⟨hParent, hGuard⟩
            rw [Summary.enabled, satisfiesSymPC] at hParent ⊢
            simp [evalSymPC, hParent, hGuard]
        continue_pc_iff := by
          intro ps input
          constructor
          · intro hEnabled
            rw [Summary.enabled, satisfiesSymPC, evalSymPC] at hEnabled
            have hBoth : evalSymPC input ps.pc = true ∧
                evalSymPC input (.not (lowerCond ps.sub ps.temps cond)) = true := by
              simpa [Bool.and_eq_true] using hEnabled
            have hGuardFalse : evalSymPC input (lowerCond ps.sub ps.temps cond) = false := by
              simpa [evalSymPC] using hBoth.2
            exact ⟨by simpa [Summary.enabled, satisfiesSymPC] using hBoth.1, hGuardFalse⟩
          · intro h
            rcases h with ⟨hParent, hGuardFalse⟩
            rw [Summary.enabled, satisfiesSymPC] at hParent ⊢
            simp [evalSymPC, hParent, hGuardFalse] }

@[inline] def execBranchContinue {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (cfg : ConcreteState Reg × TempEnv) (stmt : BranchStmt Reg) :
    ConcreteState Reg × TempEnv :=
  (branchStmtBridge ip_reg stmt).cont cfg

@[inline] def lowerBranchContinue {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (state : LowerState Reg) (stmt : BranchStmt Reg) : LowerState Reg :=
  let ps := (branchStmtBridge ip_reg stmt).lowerContinue
    { sub := state.1, pc := .true, temps := state.2 }
  (ps.sub, ps.temps)

/-- Stepping a concrete+symbolic state through a linear statement preserves
    `PartialSummaryMatches`. Abstracts the repeated `(linearStmtBridge stmt).sound`
    + `simpa` pattern from `VexLoweringCorrectness` and `VexCompTree`. -/
theorem partialSummaryMatches_linearStmt_step
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (input : ConcreteState Reg) (stmt : LinearStmt Reg)
    (concrete : ConcreteState Reg × TempEnv) (ps : PartialSummary Reg)
    (hMatch : PartialSummaryMatches input concrete ps) :
    PartialSummaryMatches input
      (execLinearStmt concrete stmt)
      { ps with sub := (lowerLinearStmt (ps.sub, ps.temps) stmt).1
                temps := (lowerLinearStmt (ps.sub, ps.temps) stmt).2 } := by
  have hStep := (linearStmtBridge stmt).sound input concrete (ps.sub, ps.temps) hMatch
  simpa [execLinearStmt, lowerLinearStmt, LowerStateMatches, PartialSummaryMatches] using hStep

end VexISA
