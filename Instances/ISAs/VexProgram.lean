import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Instances.ISAs.VexBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-- A lifted VEX program as a block map keyed by concrete instruction pointer. -/
structure Program (Reg : Type) where
  blocks : UInt64 → Option (Block Reg)

/-- Read the current instruction pointer from the concrete state. -/
def currentIp {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (state : ConcreteState Reg) : UInt64 :=
  state.read ip_reg

/-- Fetch the block at the state's current instruction pointer. -/
def fetchBlock {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg) (state : ConcreteState Reg) : Option (Block Reg) :=
  program.blocks (currentIp ip_reg state)

/-- Concrete one-step semantics for a fetched VEX block. -/
def ProgramStep {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (input output : ConcreteState Reg) : Prop :=
  ∃ block,
    fetchBlock program ip_reg input = some block ∧
    SyntaxDenotes block input output

/-- One-step semantics through lowered summary families for a fetched VEX block. -/
def ProgramSummaryStep {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg)
    (input output : ConcreteState Reg) : Prop :=
  ∃ block,
    fetchBlock program ip_reg input = some block ∧
    LoweredDenotes block input output

/-- Fetched concrete block execution and fetched lowered-summary execution coincide. -/
theorem programStep_iff_summaryStep {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg) (input output : ConcreteState Reg) :
    ProgramStep program ip_reg input output ↔
      ProgramSummaryStep program ip_reg input output := by
  constructor
  · intro h
    rcases h with ⟨block, hFetch, hStep⟩
    exact ⟨block, hFetch, (syntax_iff_lowered block input output).mp hStep⟩
  · intro h
    rcases h with ⟨block, hFetch, hStep⟩
    exact ⟨block, hFetch, (syntax_iff_lowered block input output).mpr hStep⟩

/-- Reflexive-transitive closure equivalence for fetched concrete and summary steps. -/
theorem programStep_rtc_iff_summaryStep_rtc {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (program : Program Reg) (ip_reg : Reg) (input output : ConcreteState Reg) :
    Relation.ReflTransGen (ProgramStep program ip_reg) input output ↔
      Relation.ReflTransGen (ProgramSummaryStep program ip_reg) input output := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail hpath hstep ih =>
        exact Relation.ReflTransGen.tail ih ((programStep_iff_summaryStep program ip_reg _ _).mp hstep)
  · intro h
    induction h with
    | refl => exact .refl
    | tail hpath hstep ih =>
        exact Relation.ReflTransGen.tail ih ((programStep_iff_summaryStep program ip_reg _ _).mpr hstep)

/-- Sequential composition of finite families of summaries. -/
def composeSummaryFinsets {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Finset (Summary Reg)) : Finset (Summary Reg) :=
  left.biUnion fun leftSummary => right.image (Summary.compose leftSummary)

/-- Concrete successors described by sequentially composing two summary families. -/
theorem summaryDenotes_composeSummaryFinsets_iff {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Finset (Summary Reg)) (input output : ConcreteState Reg) :
    SummaryDenotes (composeSummaryFinsets left right) input output ↔
      ∃ mid, SummaryDenotes left input mid ∧ SummaryDenotes right mid output := by
  constructor
  · intro h
    rcases h with ⟨summary, hMem, hEnabled, hApply⟩
    rcases Finset.mem_biUnion.mp hMem with ⟨leftSummary, hLeft, hRightImage⟩
    rcases Finset.mem_image.mp hRightImage with ⟨rightSummary, hRight, hCompose⟩
    subst hCompose
    let mid := Summary.apply leftSummary input
    have hEnabled' := (Summary.compose_enabled_iff leftSummary rightSummary input).1 hEnabled
    refine ⟨mid, ?_, ?_⟩
    · exact ⟨leftSummary, hLeft, hEnabled'.1, rfl⟩
    · refine ⟨rightSummary, hRight, hEnabled'.2, ?_⟩
      rw [← hApply, Summary.compose_apply]
  · rintro ⟨mid, ⟨leftSummary, hLeft, hEnabledLeft, hMid⟩, ⟨rightSummary, hRight, hEnabledRight, hOutput⟩⟩
    refine ⟨Summary.compose leftSummary rightSummary, ?_, ?_, ?_⟩
    · refine Finset.mem_biUnion.mpr ?_
      refine ⟨leftSummary, hLeft, ?_⟩
      exact Finset.mem_image.mpr ⟨rightSummary, hRight, rfl⟩
    · exact (Summary.compose_enabled_iff leftSummary rightSummary input).2 ⟨hEnabledLeft, by simpa [hMid] using hEnabledRight⟩
    · rw [Summary.compose_apply, hMid, hOutput]

/-- Set-level form of summary-family composition. -/
theorem summarySuccs_composeSummaryFinsets {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (left right : Finset (Summary Reg)) (input : ConcreteState Reg) :
    summarySuccs (composeSummaryFinsets left right) input =
      Finset.biUnion (summarySuccs left input) fun mid => summarySuccs right mid := by
  ext output
  rw [mem_summarySuccs]
  constructor
  · intro h
    rcases (summaryDenotes_composeSummaryFinsets_iff left right input output).1 h with ⟨mid, hLeft, hRight⟩
    exact Finset.mem_biUnion.mpr ⟨mid, (mem_summarySuccs left input mid).2 hLeft, (mem_summarySuccs right mid output).2 hRight⟩
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨mid, hLeft, hRight⟩
    exact (summaryDenotes_composeSummaryFinsets_iff left right input output).2
      ⟨mid, (mem_summarySuccs left input mid).1 hLeft, (mem_summarySuccs right mid output).1 hRight⟩

/-- Associativity of `Finset.biUnion` at the membership level. -/
theorem finset_biUnion_assoc {α β γ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (t : α → Finset β) (u : β → Finset γ) :
    s.biUnion (fun a => (t a).biUnion u) = (s.biUnion t).biUnion u := by
  ext x
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨a, ha, h⟩
    rcases Finset.mem_biUnion.mp h with ⟨b, hb, hx⟩
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_biUnion.mpr ⟨a, ha, hb⟩, hx⟩
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨b, hb, hx⟩
    rcases Finset.mem_biUnion.mp hb with ⟨a, ha, hb⟩
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨b, hb, hx⟩⟩

/-- Execute a fixed list of blocks concretely, threading successors forward. -/
def execBlockPath {Reg : Type} [DecidableEq Reg] [Fintype Reg] :
    List (Block Reg) → ConcreteState Reg → Finset (ConcreteState Reg)
  | [], input => {input}
  | block :: blocks, input =>
      Finset.biUnion (execBlockSuccs block input) fun mid => execBlockPath blocks mid

/-- Lower a fixed list of blocks to the composed family of path summaries. -/
def lowerBlockPathSummaries {Reg : Type} [DecidableEq Reg] [Fintype Reg] :
    List (Block Reg) → Finset (Summary Reg)
  | [] => {Summary.id}
  | block :: blocks =>
      composeSummaryFinsets (lowerBlockSummaries block) (lowerBlockPathSummaries blocks)

/-- Concrete execution of fixed lifted VEX block paths composes by append. -/
theorem execBlockPath_append {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (blocks₁ blocks₂ : List (Block Reg)) :
    ∀ input,
      execBlockPath (blocks₁ ++ blocks₂) input =
        Finset.biUnion (execBlockPath blocks₁ input) (fun mid => execBlockPath blocks₂ mid) := by
  induction blocks₁ with
  | nil =>
      intro input
      simp [execBlockPath]
  | cons block blocks ih =>
      intro input
      calc
        execBlockPath ((block :: blocks) ++ blocks₂) input
            = Finset.biUnion (execBlockSuccs block input) (fun mid => execBlockPath (blocks ++ blocks₂) mid) := by
                rfl
        _ = Finset.biUnion (execBlockSuccs block input)
              (fun mid => Finset.biUnion (execBlockPath blocks mid) (fun out => execBlockPath blocks₂ out)) := by
                simp [ih]
        _ = Finset.biUnion (Finset.biUnion (execBlockSuccs block input) (fun mid => execBlockPath blocks mid))
              (fun out => execBlockPath blocks₂ out) := by
                exact finset_biUnion_assoc (execBlockSuccs block input) (fun mid => execBlockPath blocks mid)
                  (fun out => execBlockPath blocks₂ out)
        _ = Finset.biUnion (execBlockPath (block :: blocks) input) (fun out => execBlockPath blocks₂ out) := by
                rfl

/-- ICTAC-style composition theorem for fixed lifted VEX block paths. -/
theorem summarySuccs_lowerBlockPathSummaries_eq_execBlockPath {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (blocks : List (Block Reg)) :
    ∀ input, summarySuccs (lowerBlockPathSummaries blocks) input = execBlockPath blocks input := by
  induction blocks with
  | nil =>
      intro input
      ext output
      rw [mem_summarySuccs]
      constructor
      · intro h
        rcases h with ⟨summary, hMem, hEnabled, hApply⟩
        have hMem' : summary = Summary.id := by
          simpa [lowerBlockPathSummaries] using hMem
        rcases hMem' with rfl
        simpa [execBlockPath] using hApply.symm
      · intro h
        simp [execBlockPath] at h
        rcases h with rfl
        exact ⟨Summary.id, by simp [lowerBlockPathSummaries], Summary.id_enabled _, Summary.id_apply _⟩
  | cons block blocks ih =>
      intro input
      calc
        summarySuccs (lowerBlockPathSummaries (block :: blocks)) input
            = summarySuccs (composeSummaryFinsets (lowerBlockSummaries block) (lowerBlockPathSummaries blocks)) input := by
                rfl
        _ = Finset.biUnion (summarySuccs (lowerBlockSummaries block) input) fun mid =>
              summarySuccs (lowerBlockPathSummaries blocks) mid := by
                exact summarySuccs_composeSummaryFinsets (lowerBlockSummaries block) (lowerBlockPathSummaries blocks) input
        _ = Finset.biUnion (execBlockSuccs block input) fun mid =>
              execBlockPath blocks mid := by
                simp [summarySuccs_lowerBlockSummaries_eq_execBlockSuccs, ih]
        _ = execBlockPath (block :: blocks) input := by
                rfl

/-- Executable composition theorem for fixed lifted VEX block paths. -/
theorem summarySuccs_composeLowerBlockPathSummaries_eq_execBlockPath_append
    {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (blocks₁ blocks₂ : List (Block Reg)) (input : ConcreteState Reg) :
    summarySuccs
        (composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂))
        input =
      execBlockPath (blocks₁ ++ blocks₂) input := by
  calc
    summarySuccs
        (composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂))
        input
        = Finset.biUnion (summarySuccs (lowerBlockPathSummaries blocks₁) input)
            (fun mid => summarySuccs (lowerBlockPathSummaries blocks₂) mid) := by
              exact summarySuccs_composeSummaryFinsets (lowerBlockPathSummaries blocks₁) (lowerBlockPathSummaries blocks₂) input
    _ = Finset.biUnion (execBlockPath blocks₁ input) (fun mid => execBlockPath blocks₂ mid) := by
          simp [summarySuccs_lowerBlockPathSummaries_eq_execBlockPath]
    _ = execBlockPath (blocks₁ ++ blocks₂) input := by
          symm
          exact execBlockPath_append blocks₁ blocks₂ input

end VexISA
