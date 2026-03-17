import Instances.ISAs.VexWitness
import Instances.ISAs.VexCompTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-! ## Lemma 2: `bodyEffect_spec` for `CompTree.assign (lowerBlockSub block)`.

    Abstracts the identical 4-line `bodyEffect_spec` proof in Tier6LoopWitness
    and Tier7BodyRefinement (loops whose body is `CompTree.assign (lowerBlockSub block)`). -/

theorem bodyEffect_spec_assign_lowerBlockSub
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (block : Block Reg) :
    ∀ s s' : ConcreteState Reg,
      CompTree.treeBehavior (vexSummaryISA Reg)
        (CompTree.assign (lowerBlockSub block)) s s' ↔
        s' = execBlock block s := by
  intro s s'
  simpa [CompTree.treeBehavior, assignBehavior] using
    (show (s' = applySymSub (lowerBlockSub block) s) ↔ s' = execBlock block s by
      rw [lowerBlockSub_sound block s])

/-! ## Lemma 3 (private): bodyEffect lands in execBlockSuccs when body = blockToCompTree b.

    SCR: prerequisite for `hStep_of_singleBlock`. -/

private theorem bodyEffect_mem_execBlockSuccs
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (loop : VexLoopSummary Reg) (b : Block Reg)
    (hBody : loop.body = blockToCompTree b)
    (s : ConcreteState Reg) :
    loop.bodyEffect s ∈ execBlockSuccs b s := by
  rw [← treeBehavior_blockToCompTree b s (loop.bodyEffect s)]
  rw [← hBody]
  exact (loop.bodyEffect_spec s (loop.bodyEffect s)).mpr rfl

/-! ## Lemma 4: `hStep_of_singleBlock` — derives the `hStep` hypothesis for dispatch loops.

    SCR: `dispatch_bodyPathStepRealizable` takes `hStep : ∀ s, ∃ b ∈ allBlocks,
    loop.bodyEffect s ∈ execBlockSuccs b s` as a black-box hypothesis. Without this
    lemma, every single-block-body caller must manually chain `loop.bodyEffect_spec`
    (SymExec.CircularCoinduction) with `treeBehavior_blockToCompTree`
    (Instances.ISAs.VexCompTree) — three steps that cannot be packaged any other way. -/

theorem hStep_of_singleBlock
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (loop : VexLoopSummary Reg) (b : Block Reg)
    (hBody : loop.body = blockToCompTree b) :
    ∀ s, ∃ b' ∈ ({b} : Finset (Block Reg)), loop.bodyEffect s ∈ execBlockSuccs b' s := by
  intro s
  exact ⟨b, Finset.mem_singleton_self b, bodyEffect_mem_execBlockSuccs loop b hBody s⟩

/-! ## Definitions 5a–5b: RegOnly predicates for SymExpr and SymPC.

    SCR: Mandatory foundation for `evalSymExpr_congr_of_regOnly` (lemma 6) and
    `pcSignatureWith_congr_of_regOnly` (lemma 8, Phase 3 Target 2). -/

/-- A SymExpr that only reads registers from `allowed` and contains no memory reads. -/
def SymExpr.RegOnly {Reg : Type} (allowed : Finset Reg) : SymExpr Reg → Prop
  | .const _      => True
  | .reg r        => r ∈ allowed
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e => SymExpr.RegOnly allowed e
  | .sub32 l r | .shl32 l r | .and32 l r | .or32 l r | .xor32 l r | .add64 l r | .sub64 l r
  | .xor64 l r | .and64 l r | .or64 l r | .shl64 l r | .shr64 l r | .mul64 l r | .mul32 l r =>
      SymExpr.RegOnly allowed l ∧ SymExpr.RegOnly allowed r
  | .load _ _ _   => False

/-- A SymPC is register-only when all embedded SymExprs are. -/
def SymPC.RegOnly {Reg : Type} (allowed : Finset Reg) : SymPC Reg → Prop
  | .true          => True
  | .eq l r | .lt l r | .le l r =>
      SymExpr.RegOnly allowed l ∧ SymExpr.RegOnly allowed r
  | .and φ ψ       => SymPC.RegOnly allowed φ ∧ SymPC.RegOnly allowed ψ
  | .not φ         => SymPC.RegOnly allowed φ

/-! ## Lemma 6: evalSymExpr congruence for RegOnly expressions.

    SCR: Mandatory foundation for `evalSymPC_congr_of_regOnly` (lemma 7) and
    `pcSignatureWith_congr_of_regOnly` (lemma 8). No existing congruence proof
    for `evalSymExpr` exists anywhere in the codebase. -/

private theorem evalSymExpr_congr_of_regOnly_aux
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {allowed : Finset Reg}
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    ∀ (e : SymExpr Reg), SymExpr.RegOnly allowed e → evalSymExpr s₁ e = evalSymExpr s₂ e
  | .const _, _       => rfl
  | .reg r, hr        => hRegs r hr
  | .low32 e, he      => by
      simp only [evalSymExpr]
      congr 1
      exact evalSymExpr_congr_of_regOnly_aux hRegs e he
  | .uext32 e, he     => by
      simp only [evalSymExpr]
      congr 1
      exact evalSymExpr_congr_of_regOnly_aux hRegs e he
  | .sext8to32 e, he  => by
      simp only [evalSymExpr]
      congr 1
      exact evalSymExpr_congr_of_regOnly_aux hRegs e he
  | .sext32to64 e, he => by
      simp only [evalSymExpr]
      congr 1
      exact evalSymExpr_congr_of_regOnly_aux hRegs e he
  | .sub32 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .shl32 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .and32 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .or32 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .xor32 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .add64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .sub64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .xor64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .and64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .or64 l r, ⟨hl, hr⟩  => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .shl64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .shr64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .mul64 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .mul32 l r, ⟨hl, hr⟩ => by
      simp only [evalSymExpr,
        evalSymExpr_congr_of_regOnly_aux hRegs l hl,
        evalSymExpr_congr_of_regOnly_aux hRegs r hr]
  | .load _ _ _, he   => by simp [SymExpr.RegOnly] at he

theorem evalSymExpr_congr_of_regOnly
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {allowed : Finset Reg} {e : SymExpr Reg}
    (he : SymExpr.RegOnly allowed e)
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    evalSymExpr s₁ e = evalSymExpr s₂ e :=
  evalSymExpr_congr_of_regOnly_aux hRegs e he

/-! ## Lemma 7: evalSymPC congruence for RegOnly path conditions.

    SCR: Required by `pcSignatureWith_congr_of_regOnly`. -/

theorem evalSymPC_congr_of_regOnly
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {allowed : Finset Reg} {φ : SymPC Reg}
    (hφ : SymPC.RegOnly allowed φ)
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    evalSymPC s₁ φ = evalSymPC s₂ φ := by
  induction φ with
  | true => rfl
  | eq l r =>
      rcases hφ with ⟨hl, hr⟩
      simp only [evalSymPC,
        evalSymExpr_congr_of_regOnly hl hRegs,
        evalSymExpr_congr_of_regOnly hr hRegs]
  | lt l r =>
      rcases hφ with ⟨hl, hr⟩
      simp only [evalSymPC,
        evalSymExpr_congr_of_regOnly hl hRegs,
        evalSymExpr_congr_of_regOnly hr hRegs]
  | le l r =>
      rcases hφ with ⟨hl, hr⟩
      simp only [evalSymPC,
        evalSymExpr_congr_of_regOnly hl hRegs,
        evalSymExpr_congr_of_regOnly hr hRegs]
  | and φ ψ ihφ ihψ =>
      rcases hφ with ⟨hφ', hψ'⟩
      simp only [evalSymPC, ihφ hφ', ihψ hψ']
  | not φ ih =>
      simp only [evalSymPC, ih hφ]

/-! ## Lemma 8: pcSignatureWith congruence for RegOnly closures.

    **PC-signature independence.** Phase 3 Target 2.

    If every SymPC in `closure` is register-only w.r.t. `allowed`, and `s₁` and `s₂`
    agree on all registers in `allowed`, then their PC-signatures are equal. In
    particular, registers outside `allowed` (e.g. `rsp`, stack frame, memory) do not
    affect the signature — so `BranchClassesStable` holds with `K = 2^|closure|`
    regardless of recursion depth.

    SCR: Formalizes the key claim stated informally in `VexDispatchLoop.lean` line 26:
    "Two states at different call depths reading the same character have identical PC
    signatures." No proof of this property exists anywhere else in the codebase. -/

theorem pcSignatureWith_congr_of_regOnly
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [∀ (s : ConcreteState Reg) (φ : SymPC Reg),
      Decidable ((vexSummaryISA Reg).satisfies s φ)]
    (closure : Finset (SymPC Reg))
    (allowed : Finset Reg)
    (hClosure : ∀ φ ∈ closure, SymPC.RegOnly allowed φ)
    {s₁ s₂ : ConcreteState Reg}
    (hRegs : ∀ r ∈ allowed, s₁.read r = s₂.read r) :
    pcSignatureWith (vexSummaryISA Reg) closure s₁ =
      pcSignatureWith (vexSummaryISA Reg) closure s₂ := by
  unfold pcSignatureWith
  apply Finset.filter_congr
  intro φ hφ
  simp only [vexSummaryISA, satisfiesSymPC]
  rw [evalSymPC_congr_of_regOnly (hClosure φ hφ) hRegs]

/-! ## Guard PC extraction and routing/data classification (P₀ analysis)

    `collectGuardPCsList` extracts guard PCs from `guardedChoice` nodes.
    `SymPC.isRoutingPC` classifies rip-equality guards (routing) vs data guards.
    P₀ = number of distinct data guard PCs → convergence bound K ≤ 2^P₀. -/

/-- Recursively collect all guard PCs from `guardedChoice` nodes in a CompTree. -/
def collectGuardPCsList {Sub PC : Type*} : CompTree Sub PC → List PC
  | .skip | .assign _ | .assert _ => []
  | .seq t₁ t₂ => collectGuardPCsList t₁ ++ collectGuardPCsList t₂
  | .guardedChoice guard tThen tElse =>
      guard :: (collectGuardPCsList tThen ++ collectGuardPCsList tElse)
  | .boundedIter body _ => collectGuardPCsList body

/-- Finset version of `collectGuardPCsList`. -/
def collectGuardPCs {Sub PC : Type*} [DecidableEq PC]
    (tree : CompTree Sub PC) : Finset PC :=
  (collectGuardPCsList tree).toFinset

/-- Check if a SymPC is a routing guard: `ip_reg == const` or `const == ip_reg`.
    These guards select which block to execute in the dispatch loop and do not
    contribute to the data-level specification variety (P₀). -/
def SymPC.isRoutingPC {Reg : Type} [BEq Reg] (ip_reg : Reg) : SymPC Reg → Bool
  | .eq (.reg r) (.const _) => r == ip_reg
  | .eq (.const _) (.reg r) => r == ip_reg
  | _ => false

/-- Filter a list of guard PCs to only data-level guards (non-routing). -/
def dataGuardPCsList {Reg : Type} [BEq Reg]
    (ip_reg : Reg) : List (SymPC Reg) → List (SymPC Reg) :=
  List.filter (fun pc => !pc.isRoutingPC ip_reg)

end VexISA
