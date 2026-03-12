import Instances.ISAs.VexCompTree
import Instances.ISAs.VexProofCompression
import Instances.ISAs.NextSymParserTest
import Instances.ISAs.ParserNTParserTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-!
# DispatchLoopEval — Empirical stabilization of dispatch loop branch sets

Builds a dispatch body CompTree from parsed VEX blocks, then iterates
`loopBranchSet`-style composition until the branch set stabilizes.

Includes a PC simplifier that evaluates constant-constant comparisons,
preventing syntactic noise from blocking convergence detection.
-/

/-! ## PC Simplifier

After composition, PCs may contain `eq(const a, const b)` terms from
substituting rip-routing guards. These are trivially true or false but
NOT simplified by the symbolic algebra. The simplifier evaluates them,
dropping unsatisfiable branches and collapsing trivially-true conjuncts. -/

/-- Simplify a SymPC by evaluating constant-constant comparisons.
    Returns `none` if the PC is unsatisfiable (should drop the branch). -/
partial def SymPC.simplifyConst {Reg : Type} : SymPC Reg → Option (SymPC Reg)
  | .true => some .true
  | .eq (.const a) (.const b) => if a == b then some .true else none
  | .lt (.const a) (.const b) =>
      if (a.toNat + 2^63) % 2^64 < (b.toNat + 2^63) % 2^64 then some .true else none
  | .le (.const a) (.const b) =>
      if (a.toNat + 2^63) % 2^64 ≤ (b.toNat + 2^63) % 2^64 then some .true else none
  | .eq l r => some (.eq l r)
  | .lt l r => some (.lt l r)
  | .le l r => some (.le l r)
  | .and φ ψ =>
      match (SymPC.simplifyConst φ, SymPC.simplifyConst ψ) with
      | (none, _) | (_, none) => none
      | (some .true, some ψ') => some ψ'
      | (some φ', some .true) => some φ'
      | (some φ', some ψ') => some (.and φ' ψ')
  | .not φ =>
      match SymPC.simplifyConst φ with
      | none => some .true
      | some .true => none
      | some φ' => some (.not φ')

/-- Simplify a branch's PC. Returns `none` if unsatisfiable. -/
def simplifyBranch {Sub : Type*} {Reg : Type} (b : Branch Sub (SymPC Reg)) :
    Option (Branch Sub (SymPC Reg)) :=
  match SymPC.simplifyConst b.pc with
  | none => none
  | some pc' => some ⟨b.sub, pc'⟩

/-! ## Simplified Composition

Compose two branch Finsets and simplify, dropping unsatisfiable branches. -/

/-- Compose + simplify: compose all pairs, then simplify PCs and drop
    branches with unsatisfiable constant-constant comparisons. -/
def composeBranchFinsetsSimplified {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (B₁ B₂ : Finset (Branch (SymSub Reg) (SymPC Reg))) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  let raw := composeBranchFinsets (vexSummaryISA Reg) B₁ B₂
  -- filterMap: apply simplifyBranch, keep only Some results
  raw.biUnion (fun b =>
    match simplifyBranch b with
    | none => ∅
    | some b' => {b'})

/-! ## Branch Subsumption Pruning (SMT-based)

A branch B1 is *subsumed* by B2 if they have the same substitution and B1's
path condition semantically implies B2.pc — every concrete state satisfying
B1.pc also satisfies B2.pc. B1 is then redundant (B2 covers a superset of
states with the same effect).

We use z3 (QF_BV theory) for exact semantic implication checking:
  stronger → weaker  ⟺  (stronger ∧ ¬weaker) is UNSAT
Queries are batched into a single z3 invocation per sub-hash group using
push/pop for efficiency. -/

/-- Collect the top-level conjuncts of a PC into a list. -/
partial def SymPC.conjuncts {Reg : Type} : SymPC Reg → List (SymPC Reg)
  | .and φ ψ => SymPC.conjuncts φ ++ SymPC.conjuncts ψ
  | pc => [pc]

instance : ToString Amd64Reg where
  toString
    | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rsi => "rsi"
    | .rbp => "rbp" | .rsp => "rsp" | .rdi => "rdi" | .rip => "rip"
    | .cc_op => "cc_op" | .cc_dep1 => "cc_dep1" | .cc_dep2 => "cc_dep2" | .cc_ndep => "cc_ndep"

/-- SMT-LIB2 width suffix for memory operations. -/
def Width.toSMTWidth : Width → String
  | .w8 => "8" | .w16 => "16" | .w32 => "32" | .w64 => "64"

mutual
/-- Encode a SymExpr as an SMT-LIB2 bitvector expression (64-bit). -/
partial def SymExpr.toSMTLib {Reg : Type} [ToString Reg] : SymExpr Reg → String
  | .const v => s!"(_ bv{v.toNat} 64)"
  | .reg r => s!"reg_{toString r}"
  | .low32 e => s!"((_ zero_extend 32) ((_ extract 31 0) {SymExpr.toSMTLib e}))"
  | .uext32 e => s!"((_ zero_extend 32) ((_ extract 31 0) {SymExpr.toSMTLib e}))"
  | .sext8to32 e => s!"((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) {SymExpr.toSMTLib e})))"
  | .sext32to64 e => s!"((_ sign_extend 32) ((_ extract 31 0) {SymExpr.toSMTLib e}))"
  | .sub32 l r => s!"((_ zero_extend 32) (bvsub ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .shl32 l r => s!"((_ zero_extend 32) (bvshl ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .add64 l r => s!"(bvadd {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .sub64 l r => s!"(bvsub {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .xor64 l r => s!"(bvxor {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .and64 l r => s!"(bvand {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .or64 l r => s!"(bvor {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .shl64 l r => s!"(bvshl {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .shr64 l r => s!"(bvlshr {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .load w m addr => s!"(load_{Width.toSMTWidth w} {SymMem.toSMTLib m} {SymExpr.toSMTLib addr})"

/-- Encode a SymMem as an SMT-LIB2 expression (uninterpreted sort). -/
partial def SymMem.toSMTLib {Reg : Type} [ToString Reg] : SymMem Reg → String
  | .base => "base_mem"
  | .store w m addr val =>
    s!"(store_{Width.toSMTWidth w} {SymMem.toSMTLib m} {SymExpr.toSMTLib addr} {SymExpr.toSMTLib val})"
end

/-- Encode a SymPC as an SMT-LIB2 boolean formula.
    Uses unsigned comparison (bvult/bvule) matching evalSymPC semantics. -/
partial def SymPC.toSMTLib {Reg : Type} [ToString Reg] : SymPC Reg → String
  | .true => "true"
  | .eq l r => s!"(= {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .lt l r => s!"(bvult {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .le l r => s!"(bvule {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .and φ ψ => s!"(and {SymPC.toSMTLib φ} {SymPC.toSMTLib ψ})"
  | .not φ => s!"(not {SymPC.toSMTLib φ})"

/-- Collect all register names appearing in a SymPC (for variable declarations). -/
partial def SymExpr.collectRegNames {Reg : Type} [ToString Reg] [BEq Reg] [Hashable Reg]
    : SymExpr Reg → Std.HashSet String → Std.HashSet String
  | .const _, s => s
  | .reg r, s => s.insert s!"reg_{toString r}"
  | .low32 e, s => SymExpr.collectRegNames e s
  | .uext32 e, s => SymExpr.collectRegNames e s
  | .sext8to32 e, s => SymExpr.collectRegNames e s
  | .sext32to64 e, s => SymExpr.collectRegNames e s
  | .sub32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .shl32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .add64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .sub64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .xor64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .and64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .or64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .shl64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .shr64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .load _ _ addr, s => SymExpr.collectRegNames addr s

partial def SymPC.collectRegNames {Reg : Type} [ToString Reg] [BEq Reg] [Hashable Reg]
    : SymPC Reg → Std.HashSet String → Std.HashSet String
  | .true, s => s
  | .eq l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .lt l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .le l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .and φ ψ, s => SymPC.collectRegNames ψ (SymPC.collectRegNames φ s)
  | .not φ, s => SymPC.collectRegNames φ s

mutual
/-- Check if a SymExpr mentions any memory loads. -/
partial def SymExpr.hasLoad {Reg : Type} : SymExpr Reg → Bool
  | .load _ _ _ => true
  | .const _ | .reg _ => false
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e => SymExpr.hasLoad e
  | .sub32 l r | .shl32 l r | .add64 l r | .sub64 l r | .xor64 l r
  | .and64 l r | .or64 l r | .shl64 l r | .shr64 l r => SymExpr.hasLoad l || SymExpr.hasLoad r

partial def SymMem.hasLoad {Reg : Type} : SymMem Reg → Bool
  | .base => false
  | .store _ m addr val => SymMem.hasLoad m || SymExpr.hasLoad addr || SymExpr.hasLoad val
end

partial def SymPC.hasLoad {Reg : Type} : SymPC Reg → Bool
  | .true => false
  | .eq l r | .lt l r | .le l r => SymExpr.hasLoad l || SymExpr.hasLoad r
  | .and φ ψ => SymPC.hasLoad φ || SymPC.hasLoad ψ
  | .not φ => SymPC.hasLoad φ

mutual
/-- Collect all registers referenced in a SymExpr (as Reg values). -/
partial def SymExpr.collectRegsHS {Reg : Type} [BEq Reg] [Hashable Reg]
    : SymExpr Reg → Std.HashSet Reg → Std.HashSet Reg
  | .const _, s => s
  | .reg r, s => s.insert r
  | .low32 e, s => SymExpr.collectRegsHS e s
  | .uext32 e, s => SymExpr.collectRegsHS e s
  | .sext8to32 e, s => SymExpr.collectRegsHS e s
  | .sext32to64 e, s => SymExpr.collectRegsHS e s
  | .sub32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .shl32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .add64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .sub64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .xor64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .and64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .or64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .shl64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .shr64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .load _ m addr, s => SymExpr.collectRegsHS addr (SymMem.collectRegsHS m s)

/-- Collect all registers referenced in a SymMem. -/
partial def SymMem.collectRegsHS {Reg : Type} [BEq Reg] [Hashable Reg]
    : SymMem Reg → Std.HashSet Reg → Std.HashSet Reg
  | .base, s => s
  | .store _ m addr val, s =>
    SymExpr.collectRegsHS val (SymExpr.collectRegsHS addr (SymMem.collectRegsHS m s))
end

/-- Collect all registers referenced in a SymPC. -/
partial def SymPC.collectRegsHS {Reg : Type} [BEq Reg] [Hashable Reg]
    : SymPC Reg → Std.HashSet Reg → Std.HashSet Reg
  | .true, s => s
  | .eq l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .lt l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .le l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .and φ ψ, s => SymPC.collectRegsHS ψ (SymPC.collectRegsHS φ s)
  | .not φ, s => SymPC.collectRegsHS φ s

/-- Build the SMT-LIB2 preamble: logic, register declarations, and memory
    declarations if any PCs involve loads. -/
def smtPreamble (regNames : Std.HashSet String) (needsMem : Bool) : String := Id.run do
  let mut s := "(set-logic QF_UFBV)\n"
  for name in regNames do
    s := s ++ s!"(declare-const {name} (_ BitVec 64))\n"
  if needsMem then
    s := s ++ "(declare-sort Mem 0)\n"
    s := s ++ "(declare-const base_mem Mem)\n"
    for w in ["8", "16", "32", "64"] do
      s := s ++ s!"(declare-fun load_{w} (Mem (_ BitVec 64)) (_ BitVec 64))\n"
      s := s ++ s!"(declare-fun store_{w} (Mem (_ BitVec 64) (_ BitVec 64)) Mem)\n"
  return s

/-! ## PC-Signature Equivalence Class Dedup

Two branches with the same substitution and the same PC signature (which guard PCs
from the closure they satisfy) will behave identically in all future compositions.
The convergence proof (`dispatch_branchClassesStable`) shows K ≤ 2^|closure| because
there are only that many distinct signature classes.

By deduplicating on (sub, signature), we collapse exponentially many branches into
at most 2^|closure| classes per distinct substitution, preventing the ~5x/iteration
blowup that causes OOM. -/

/-- Check if a guard PC is a rip-routing guard (eq (reg ip) (const addr)).
    These are determined by control flow path, not by data — filtering them
    out gives the data-only closure (P₀ from the convergence plan). -/
def isRipGuardPC {Reg : Type} [BEq Reg] (ip_reg : Reg) : SymPC Reg → Bool
  | .eq (.reg r) (.const _) => r == ip_reg
  | .eq (.const _) (.reg r) => r == ip_reg
  | _ => false

/-- Extract the closure from body branches: all distinct atomic conjuncts
    appearing in any body branch's PC.
    If `dataOnly` is true, filters out rip-routing guards (eq rip (const addr)),
    keeping only data-level guard PCs. This gives P₀ from the convergence plan. -/
def extractClosure {Reg : Type} [BEq Reg] [BEq (SymPC Reg)] [Hashable (SymPC Reg)]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (dataOnly : Bool := false) :
    Array (SymPC Reg) × Nat × Nat := Id.run do
  let mut seen : Std.HashSet (SymPC Reg) := {}
  let mut result : Array (SymPC Reg) := #[]
  let mut ripCount : Nat := 0
  let mut dataCount : Nat := 0
  for b in bodyArr do
    let conjuncts := SymPC.conjuncts b.pc
    for c in conjuncts do
      unless seen.contains c do
        seen := seen.insert c
        if isRipGuardPC ip_reg c then
          ripCount := ripCount + 1
          unless dataOnly do
            result := result.push c
        else
          dataCount := dataCount + 1
          result := result.push c
  return (result, ripCount, dataCount)

/-- Compute the PC signature of a branch w.r.t. a closure.
    Returns a list of bools: for each guard PC in the closure, does the branch's
    PC syntactically imply it?

    This is the computational analog of `pcSignatureWith` from VexDispatchLoop.lean,
    which filters the closure to the subset satisfied by a concrete state.
    Here we work purely syntactically: a branch's PC "satisfies" a guard PC if
    the branch's PC syntactically implies it (all conjuncts of the guard appear
    in the branch's conjuncts). -/
def computePCSignature {Reg : Type} [DecidableEq Reg] [Hashable (SymPC Reg)]
    (closure : Array (SymPC Reg)) (pc : SymPC Reg) : List Bool :=
  -- Pre-compute conjuncts of pc into a HashSet for O(1) membership checks.
  -- This is called O(composed_size) times per iteration, so efficiency matters.
  let pcConjList := SymPC.conjuncts pc
  let pcConjSet : Std.HashSet (SymPC Reg) :=
    pcConjList.foldl (fun s c => s.insert c) {}
  closure.toList.map fun guardPC =>
    match guardPC with
    | .true => true  -- everything implies .true
    | _ => pcConjSet.contains guardPC

/-- Hash a PC signature (list of bools) for use as a HashMap key. -/
def hashPCSignature (sig : List Bool) : UInt64 :=
  sig.foldl (fun acc b => mixHash acc (if b then 1 else 0)) 7

/-- Key for PC-signature dedup: combines substitution hash with PC signature.
    Two branches with the same dedup key are in the same equivalence class. -/
structure SigDedupKey where
  subHash : UInt64
  sig : List Bool
  deriving BEq

instance : Hashable SigDedupKey where
  hash k := mixHash k.subHash (hashPCSignature k.sig)

/-- Dedup an array of branches by (sub, PC-signature) equivalence class.
    Returns (dedupedArray, collapsedCount). -/
def dedupBySignature {Reg : Type} [DecidableEq Reg] [Hashable Reg] [EnumReg Reg]
    (closure : Array (SymPC Reg))
    (branches : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat := Id.run do
  let mut seen : Std.HashSet SigDedupKey := {}
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut collapsed : Nat := 0
  for b in branches do
    let sig := computePCSignature closure b.pc
    let key : SigDedupKey := ⟨hash b.sub, sig⟩
    if seen.contains key then
      collapsed := collapsed + 1
    else
      seen := seen.insert key
      result := result.push b
  return (result, collapsed)

/-! ## HashSet-based Stabilization (fast path)

Uses `Std.HashSet` for O(1) membership checks instead of Finset's O(n) linear scan.
The Hashable instances on SymExpr/SymPC/SymSub/Branch enable this. -/

/-- Extract the rip-guard address from a branch's PC.
    Body branches from `flatBodyDenot` have PCs of the form
    `and (eq (reg ip) (const addr)) rest` or just `eq (reg ip) (const addr)`.
    After stabilization rounds, the outermost rip guard is always the left
    conjunct (inner rip guards simplify to true/false via simplifyConst). -/
def extractRipGuard {Reg : Type} [BEq Reg] (ip_reg : Reg) :
    SymPC Reg → Option UInt64
  | .and (.eq (.reg r) (.const addr)) _ => if r == ip_reg then some addr else none
  | .eq (.reg r) (.const addr) => if r == ip_reg then some addr else none
  | _ => none

/-- Extract the rip target from a body branch's substitution.
    If the branch maps ip_reg to a constant, that's the next block address. -/
def extractRipTarget {Reg : Type} (ip_reg : Reg) (sub : SymSub Reg) :
    Option UInt64 :=
  match sub.regs ip_reg with
  | .const addr => some addr
  | _ => none

/-- Compose body branches with frontier branches, simplify, return as Array.
    Uses direct iteration instead of Finset.biUnion/image.
    Returns (result, totalPairs, droppedCount). -/
def composeBranchArraySimplified {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat × Nat := Id.run do
  let isa := vexSummaryISA Reg
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  for b1 in bodyArr do
    for b2 in frontierArr do
      let composed := b1.compose isa b2
      match simplifyBranch composed with
      | none => dropped := dropped + 1
      | some b' => result := result.push b'
  return (result, bodyArr.size * frontierArr.size, dropped)

/-- Rip-indexed composition: only compose body branches with frontier branches
    whose rip-guard matches the body branch's rip target.

    In the dispatch loop, `body.compose(frontier)` produces:
      pc = and body.pc (lift body.sub frontier.pc)
    The frontier's rip guard `eq (reg rip) (const addr)` gets lifted to
    `eq (body.sub.regs rip) (const addr)`. If body.sub.regs rip = const X,
    this is `eq (const X) (const addr)` — satisfiable iff X == addr.

    By indexing frontier branches by their rip-guard address and looking up
    body.sub.regs rip, we skip ~94% of compositions that would be dropped.

    Returns (result, totalPairs, skippedByIndex, droppedBySimplify). -/
def composeBranchArrayIndexed {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg) (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat × Nat × Nat := Id.run do
  let isa := vexSummaryISA Reg
  -- Build frontier index: rip-guard addr → array of frontier branches
  let mut frontierByRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  let mut frontierNoRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  for f in frontierArr do
    match extractRipGuard ip_reg f.pc with
    | some addr =>
      let arr := frontierByRip.getD addr #[]
      frontierByRip := frontierByRip.insert addr (arr.push f)
    | none => frontierNoRip := frontierNoRip.push f
  -- Compose using index
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  let totalPairs := bodyArr.size * frontierArr.size
  for b in bodyArr do
    -- Determine which frontier branches this body can reach
    let compatible := match extractRipTarget ip_reg b.sub with
      | some target => (frontierByRip.getD target #[]) ++ frontierNoRip
      | none => frontierArr  -- can't determine target, fall back to all
    for f in compatible do
      composed_count := composed_count + 1
      let composed := b.compose isa f
      match simplifyBranch composed with
      | none => dropped := dropped + 1
      | some b' => result := result.push b'
  let skipped := totalPairs - composed_count
  return (result, composed_count, skipped, dropped)

/-- Per-chunk composition result for parallel merge. -/
structure ChunkResult (Sub PC : Type*) where
  branches : Array (Branch Sub PC)
  composed : Nat
  dropped : Nat

/-- Compose a chunk of body branches with the frontier (rip-indexed).
    Pure function — no shared mutable state, safe to run in parallel. -/
def composeChunk {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg) (bodyChunk : Array (Branch (SymSub Reg) (SymPC Reg)))
    (frontierByRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))))
    (frontierNoRip : Array (Branch (SymSub Reg) (SymPC Reg)))
    (frontierAll : Array (Branch (SymSub Reg) (SymPC Reg))) :
    ChunkResult (SymSub Reg) (SymPC Reg) := Id.run do
  let isa := vexSummaryISA Reg
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  for b in bodyChunk do
    let compatible := match extractRipTarget ip_reg b.sub with
      | some target => (frontierByRip.getD target #[]) ++ frontierNoRip
      | none => frontierAll
    for f in compatible do
      composed_count := composed_count + 1
      let composed := b.compose isa f
      match simplifyBranch composed with
      | none => dropped := dropped + 1
      | some b' => result := result.push b'
  return ⟨result, composed_count, dropped⟩

/-- Split an array into N roughly-equal chunks. -/
def splitIntoChunks {α : Type} (arr : Array α) (n : Nat) : Array (Array α) := Id.run do
  if n == 0 || arr.size == 0 then return #[arr]
  let chunkSize := (arr.size + n - 1) / n
  let mut chunks : Array (Array α) := #[]
  let mut i := 0
  while i < arr.size do
    let endIdx := min (i + chunkSize) arr.size
    chunks := chunks.push (arr.extract i endIdx)
    i := endIdx
  return chunks

/-- Parallel rip-indexed composition with dedup.
    Splits body array into chunks, composes each chunk in parallel via IO.asTask,
    then merges results into the HashSet sequentially.
    Returns (newBranches, updatedCurrent, pairsComposed, skipped, dropped, dupes). -/
def composeAndDedupParallel {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg]
    (ip_reg : Reg) (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)))
    (numWorkers : Nat := 8) :
    IO (Array (Branch (SymSub Reg) (SymPC Reg)) × Std.HashSet (Branch (SymSub Reg) (SymPC Reg))
      × Nat × Nat × Nat × Nat) := do
  -- Build frontier index (shared across workers, immutable)
  let (frontierByRip, frontierNoRip) ← do
    let mut byRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
    let mut noRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for f in frontierArr do
      match extractRipGuard ip_reg f.pc with
      | some addr =>
        let arr := byRip.getD addr #[]
        byRip := byRip.insert addr (arr.push f)
      | none => noRip := noRip.push f
    pure (byRip, noRip)
  -- Split body into chunks and spawn tasks
  let chunks := splitIntoChunks bodyArr numWorkers
  let tasks ← chunks.mapM fun chunk =>
    IO.asTask (prio := .dedicated) do
      return composeChunk ip_reg chunk frontierByRip frontierNoRip frontierArr
  -- Collect results
  let results ← tasks.mapM fun task => do
    let r ← IO.wait task
    IO.ofExcept r
  -- Merge into HashSet (sequential — avoids concurrent mutation)
  let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut cur := current
  let mut totalComposed : Nat := 0
  let mut totalDropped : Nat := 0
  let mut dupes : Nat := 0
  for r in results do
    totalComposed := totalComposed + r.composed
    totalDropped := totalDropped + r.dropped
    for b in r.branches do
      if cur.contains b then
        dupes := dupes + 1
      else
        newBranches := newBranches.push b
        cur := cur.insert b
  let totalPairs := bodyArr.size * frontierArr.size
  let skipped := totalPairs - totalComposed
  return (newBranches, cur, totalComposed, skipped, totalDropped, dupes)

/-- Fast incremental stabilization using HashSet for O(1) membership.
    Single-threaded rip-indexed composition with inline dedup.
    Includes PC-signature equivalence class dedup and subsumption pruning. -/
def computeStabilizationHS {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg] [ToString Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) (logFile : Option System.FilePath := none) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  -- Extract the closure: all distinct atomic guard PCs from body branches.
  -- dataOnly=true filters rip-routing guards, keeping only data PCs (P₀).
  let (closure, ripCount, dataCount) := extractClosure ip_reg bodyArr (dataOnly := true)
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  current := current.insert initBranch
  -- sigSeen tracks (sub, signature) classes across ALL iterations.
  -- A new branch is only added if its signature class hasn't been seen before.
  let mut sigSeen : Std.HashSet SigDedupKey := {}
  let initSig := computePCSignature closure initBranch.pc
  sigSeen := sigSeen.insert ⟨hash initBranch.sub, initSig⟩
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[initBranch]
  -- allBranchesBySub: sub hash → array of branches, for efficient subsumption check
  let mut allBranchesBySub : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  allBranchesBySub := allBranchesBySub.insert (hash initBranch.sub) #[initBranch]
  let log (msg : String) : IO Unit := do
    IO.println msg
    if let some path := logFile then
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn msg
  log s!"  closure: total={ripCount + dataCount} rip={ripCount} data={dataCount} (using data-only={closure.size})"
  -- Collect registers referenced by data PCs (for projection/widening diagnostic)
  let mut dataPCRegs : Std.HashSet Reg := {}
  let mut dataPCsHaveLoads := false
  for pc in closure do
    dataPCRegs := SymPC.collectRegsHS pc dataPCRegs
    if SymPC.hasLoad pc then dataPCsHaveLoads := true
  let dataPCRegsArr := dataPCRegs.toArray
  log s!"  data PC regs: [{", ".intercalate (dataPCRegsArr.toList.map toString)}] ({dataPCRegsArr.size} regs, loads={dataPCsHaveLoads})"
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    let (composed, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr frontier
    -- Inline dedup: exact-match via HashSet + signature-class via sigSeen
    let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut dupes : Nat := 0
    let mut sigCollapsed : Nat := 0
    for b in composed do
      if current.contains b then
        dupes := dupes + 1
      else
        -- Check signature-class dedup
        let sig := computePCSignature closure b.pc
        let key : SigDedupKey := ⟨hash b.sub, sig⟩
        if sigSeen.contains key then
          sigCollapsed := sigCollapsed + 1
        else
          sigSeen := sigSeen.insert key
          newBranches := newBranches.push b
    -- Semantic subsumption via z3: batch check new branches against existing
    let t_prune_start ← IO.monoMsNow
    let mut prunedCount : Nat := 0
    -- Build (stronger_pc, weaker_pc) pairs and track which new branch each belongs to
    let mut pcPairs : Array (SymPC Reg × SymPC Reg) := #[]
    let mut queryBranchIdx : Array Nat := #[]
    let mut branchIdx : Nat := 0
    for bi in newBranches do
      let h := hash bi.sub
      let existingGroup := allBranchesBySub.getD h #[]
      for bj in existingGroup do
        if bi.pc != bj.pc then
          pcPairs := pcPairs.push (bi.pc, bj.pc)
          queryBranchIdx := queryBranchIdx.push branchIdx
      branchIdx := branchIdx + 1
    -- Call z3 with all queries at once
    let mut subsumedSet : Std.HashSet Nat := {}
    if pcPairs.size > 0 then
      -- Collect register names and check for memory ops
      let mut regNames : Std.HashSet String := {}
      let mut needsMem := false
      for (stronger, weaker) in pcPairs do
        regNames := SymPC.collectRegNames stronger regNames
        regNames := SymPC.collectRegNames weaker regNames
        if SymPC.hasLoad stronger || SymPC.hasLoad weaker then needsMem := true
      -- Generate SMT-LIB2 script
      let mut script := smtPreamble regNames needsMem
      for (stronger, weaker) in pcPairs do
        script := script ++ "(push)\n"
        script := script ++ s!"(assert (and {SymPC.toSMTLib stronger} (not {SymPC.toSMTLib weaker})))\n"
        script := script ++ "(check-sat)\n"
        script := script ++ "(pop)\n"
      script := script ++ "(exit)\n"
      -- Write and invoke z3
      let tmpFile : System.FilePath := ".lake/smt_subsumption.smt2"
      IO.FS.writeFile tmpFile script
      let result ← IO.Process.output {
        cmd := "z3"
        args := #[tmpFile.toString]
      }
      -- Parse results
      let lines := result.stdout.splitOn "\n" |>.filter (· != "")
      for i in [:pcPairs.size] do
        if h : i < lines.length then
          if lines[i] == "unsat" then
            if h2 : i < queryBranchIdx.size then
              subsumedSet := subsumedSet.insert queryBranchIdx[i]
      log s!"    z3: {pcPairs.size} queries, {lines.length} results, {subsumedSet.size} subsumed"
    -- Filter new branches
    let mut survivingNew : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    branchIdx := 0
    for bi in newBranches do
      if subsumedSet.contains branchIdx then
        prunedCount := prunedCount + 1
      else
        survivingNew := survivingNew.push bi
      branchIdx := branchIdx + 1
    newBranches := survivingNew
    -- Update tracking structures with surviving new branches
    for b in newBranches do
      current := current.insert b
      let h := hash b.sub
      let arr := allBranchesBySub.getD h #[]
      allBranchesBySub := allBranchesBySub.insert h (arr.push b)
    let t_end ← IO.monoMsNow
    -- Count distinct subs in frontier (diagnostic: how many "paths"?)
    let mut frontierSubs : Std.HashSet UInt64 := {}
    let mut frontierSubsNoRip : Std.HashSet UInt64 := {}
    let mut projectedSubs : Std.HashSet UInt64 := {}
    for b in newBranches do
      frontierSubs := frontierSubs.insert (hash b.sub)
      let noRipSub : SymSub Reg := { b.sub with regs := fun r => if r == ip_reg then .const 0 else b.sub.regs r }
      frontierSubsNoRip := frontierSubsNoRip.insert (hash noRipSub)
      -- Project sub onto only data-PC registers (widening equivalence class)
      let mut projHash : UInt64 := 0
      for r in dataPCRegsArr do
        projHash := mixHash projHash (hash (b.sub.regs r))
      if dataPCsHaveLoads then projHash := mixHash projHash (hash b.sub.mem)
      projectedSubs := projectedSubs.insert projHash
    log s!"  K={k}: |S|={current.size} |frontier|={frontier.size} |new|={newBranches.size} |distinct_subs|={frontierSubs.size} |no_rip|={frontierSubsNoRip.size} |proj|={projectedSubs.size} pairs={pairsComposed} skipped={skipped} dropped={dropped} dupes={dupes} sig_collapsed={sigCollapsed} pruned={prunedCount} compose={t_prune_start - t_start}ms prune={t_end - t_prune_start}ms total={t_end - t_start}ms"
    if newBranches.size == 0 then
      return some (k, current.size)
    frontier := newBranches
  return none

/-! ## Stabilization Computation -/

/-- Naive stabilization: composes bodyDenot with the FULL accumulated set each
    iteration. Kept for correctness comparison. -/
def computeStabilizationNaive {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyDenot : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let mut current : Finset (Branch (SymSub Reg) (SymPC Reg)) := {Branch.skip isa}
  for k in List.range maxIter do
    let composed := composeBranchFinsetsSimplified bodyDenot current
    let next := current ∪ composed
    if k % 5 == 0 || next == current then
      IO.println s!"  K={k}: |S| = {current.card}, |new| = {(next \ current).card}"
    if next == current then
      return some (k, current.card)
    current := next
  return none

/-- Incremental stabilization: only composes bodyDenot with the frontier
    (branches added in the previous round), not the full accumulated set.

    Correctness: composition distributes over union in the second argument.
    If `current = old ∪ frontier`, then `body ⊗ current = (body ⊗ old) ∪ (body ⊗ frontier)`.
    Since `body ⊗ old ⊆ current` (computed in prior rounds), only `body ⊗ frontier`
    can produce genuinely new branches. -/
def computeStabilization {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (bodyDenot : Finset (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) (logFile : Option System.FilePath := none) : IO (Option (Nat × Nat)) := do
  let isa := vexSummaryISA Reg
  let init : Finset (Branch (SymSub Reg) (SymPC Reg)) := {Branch.skip isa}
  let mut current := init
  let mut frontier := init
  let log (msg : String) : IO Unit := do
    IO.println msg
    if let some path := logFile then
      let h ← IO.FS.Handle.mk path .append
      h.putStrLn msg
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    let composed := composeBranchFinsetsSimplified bodyDenot frontier
    let t_compose ← IO.monoMsNow
    let newBranches := composed \ current
    let t_diff ← IO.monoMsNow
    log s!"  K={k}: |S|={current.card} |frontier|={frontier.card} |composed|={composed.card} |new|={newBranches.card} compose={t_compose - t_start}ms diff={t_diff - t_compose}ms"
    if newBranches.card == 0 then
      return some (k, current.card)
    current := current ∪ newBranches
    frontier := newBranches
  return none

/-! ## Dispatch Body Construction -/

/-- Build the dispatch body CompTree from a list of (address, block) pairs.
    Each block is guarded by `rip == address`. -/
def buildDispatchBody {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (blocks : List (UInt64 × Block Reg)) :
    CompTree (SymSub Reg) (SymPC Reg) :=
  blocks.foldr (fun (addr, block) acc =>
    CompTree.guardedChoice
      (SymPC.eq (SymExpr.reg ip_reg) (SymExpr.const addr))
      (blockToCompTree block)
      acc)
    CompTree.skip

/-- Compute bodyDenot as a flat union of per-block branches with rip guards.
    Avoids the nested negation chains from `denot` on nested guardedChoice. -/
def flatBodyDenot {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (ip_reg : Reg) (blocks : List (UInt64 × Block Reg)) :
    Finset (Branch (SymSub Reg) (SymPC Reg)) :=
  let isa := vexSummaryISA Reg
  blocks.foldl (fun acc (addr, block) =>
    let blockDenot := CompTree.denot isa (blockToCompTree block)
    let guard : Branch (SymSub Reg) (SymPC Reg) :=
      ⟨isa.id_sub, SymPC.eq (SymExpr.reg ip_reg) (SymExpr.const addr)⟩
    acc ∪ composeBranchFinsets isa {guard} blockDenot)
    ∅

/-- Convert Finset to Array at runtime. Multiset is Quot (List.Perm),
    which is erased to List at runtime. unsafeCast recovers it. -/
private unsafe def finsetToArrayImpl {α : Type} (s : Finset α) : Array α :=
  (unsafeCast s.val : List α).toArray

@[implemented_by finsetToArrayImpl]
private def finsetToArray {α : Type} (s : Finset α) : Array α :=
  #[]

/-! ## Parse blocks with addresses -/

/-- Parse block strings into (address, block) pairs. -/
def parseBlocksWithAddresses (blockStrs : List String) :
    Except String (List (UInt64 × Block Amd64Reg)) :=
  blockStrs.mapM fun text => do
    let ip ← extractIMarkIP text
    let block ← parseIRSB text
    return (ip, block)

/-! ## Run stabilization on next_sym -/

/-- Main entry point for dispatch loop evaluation.
    Extracted from #eval so it can be used by both #eval and native exe. -/
def dispatchLoopEvalMain : IO Unit := do
  let logPath : System.FilePath := ".lake/stabilization.log"
  IO.FS.writeFile logPath ""
  let log (msg : String) : IO Unit := do
    IO.println msg
    let h ← IO.FS.Handle.mk logPath .append
    h.putStrLn msg
  log "=== Dispatch Loop Stabilization: next_sym (sig-dedup + subsumption pruning) ==="
  match parseBlocksWithAddresses nextSymBlocks with
  | .error e => log s!"PARSE ERROR: {e}"
  | .ok allPairs =>
    log s!"Total blocks available: {allPairs.length}"
    log "N, |bodyDenot|, K, |S_final|, bodyDenot_ms, stabilization_ms"
    for n in [55, 60] do
      if n > allPairs.length then
        log s!"{n}, ---, SKIP (only {allPairs.length} blocks), ---, ---, ---"
      else
        let pairs := allPairs.take n
        let t0 ← IO.monoMsNow
        let body := flatBodyDenot Amd64Reg.rip pairs
        let t1 ← IO.monoMsNow
        let bodyArr := finsetToArray body
        log s!"  N={n}: |bodyDenot|={bodyArr.size}, starting stabilization..."
        match ← computeStabilizationHS Amd64Reg.rip bodyArr 200 logPath with
        | some (k, card) =>
          let t2 ← IO.monoMsNow
          log s!"{n}, {body.card}, {k}, {card}, {t1 - t0}, {t2 - t1}"
        | none =>
          let t2 ← IO.monoMsNow
          log s!"{n}, {body.card}, DNF, DNF, {t1 - t0}, {t2 - t1}"
