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

/-! ## Load-After-Store Memory Simplification

After composition, memory terms grow as chains of `store` operations.
`load(W, store(W, mem, addr, val), addr')` can be simplified:
- If W matches and addr == addr' (syntactically): result is `val`
- If addr and addr' are different constants: skip the store, recurse into mem
- Otherwise: keep as-is (can't determine statically)

This is an EXACT optimization — it evaluates what the concrete semantics would
compute, just at the symbolic level. No information is lost. Combined with
simplifyConst (which handles const-const comparisons), this collapses the
expression chains that cause unbounded growth in iterative composition. -/

/-! ## Expression Diagnostics -/

mutual
partial def exprNodeCount {Reg : Type} : SymExpr Reg → Nat
  | .const _ => 1
  | .reg _ => 1
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x => 1 + exprNodeCount x
  | .sub32 a b | .shl32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b =>
    1 + exprNodeCount a + exprNodeCount b
  | .load _ m addr => 1 + memNodeCount m + exprNodeCount addr

partial def memNodeCount {Reg : Type} : SymMem Reg → Nat
  | .base => 1
  | .store _ m addr val => 1 + memNodeCount m + exprNodeCount addr + exprNodeCount val

partial def exprUnresolvedLoads {Reg : Type} : SymExpr Reg → Nat
  | .const _ | .reg _ => 0
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x => exprUnresolvedLoads x
  | .sub32 a b | .shl32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b =>
    exprUnresolvedLoads a + exprUnresolvedLoads b
  | .load _ m addr => (match m with | .base => 0 | _ => 1) + memUnresolvedLoads m + exprUnresolvedLoads addr

partial def memUnresolvedLoads {Reg : Type} : SymMem Reg → Nat
  | .base => 0
  | .store _ m addr val => memUnresolvedLoads m + exprUnresolvedLoads addr + exprUnresolvedLoads val

partial def exprSummary {Reg : Type} [ToString Reg] : SymExpr Reg → Nat → String
  | .const v, _ => s!"C({v})"
  | .reg r, _ => s!"R({r})"
  | _, 0 => s!"..."
  | .low32 x, d => s!"lo32({exprSummary x (d-1)})"
  | .uext32 x, d => s!"zx32({exprSummary x (d-1)})"
  | .sext8to32 x, d => s!"sx8({exprSummary x (d-1)})"
  | .sext32to64 x, d => s!"sx32({exprSummary x (d-1)})"
  | .add64 a b, d => s!"add({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .sub64 a b, d => s!"sub({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .xor64 a b, d => s!"xor({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .and64 a b, d => s!"and({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .or64 a b, d => s!"or({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .shl64 a b, d => s!"shl({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .shr64 a b, d => s!"shr({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .sub32 a b, d => s!"sub32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .shl32 a b, d => s!"shl32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .load w m addr, d => s!"ld{w.byteCount*8}(mem[{memNodeCount m}],{exprSummary addr (d-1)})"
end

mutual
/-- Fold nested add64/sub64 with constants.
    Normalizes stack arithmetic so load/store addresses match.
    e.g. add64(add64(x, C(8)), C(8)) → add64(x, C(16))
         sub64(sub64(x, C(8)), C(16)) → sub64(x, C(24))
         sub64(add64(x, C(16)), C(8)) → add64(x, C(8)) -/
partial def foldAdd64 {Reg : Type} [DecidableEq Reg]
    (a b : SymExpr Reg) : SymExpr Reg :=
  match a, b with
  -- const + const
  | .const x, .const y => .const (x + y)
  -- add(x, c1) + c2 → add(x, c1+c2)
  | .add64 x (.const c1), .const c2 =>
    let c := c1 + c2
    if c == 0 then x else .add64 x (.const c)
  -- c1 + add(x, c2) → add(x, c1+c2)
  | .const c1, .add64 x (.const c2) =>
    let c := c1 + c2
    if c == 0 then x else .add64 x (.const c)
  -- sub(x, c1) + c2 → if c2 ≥ c1: add(x, c2-c1), else sub(x, c1-c2)
  | .sub64 x (.const c1), .const c2 =>
    if c2 == c1 then x
    else if c2 > c1 then .add64 x (.const (c2 - c1))
    else .sub64 x (.const (c1 - c2))
  -- c1 + sub(x, c2) → same
  | .const c1, .sub64 x (.const c2) =>
    if c1 == c2 then x
    else if c1 > c2 then .add64 x (.const (c1 - c2))
    else .sub64 x (.const (c2 - c1))
  -- x + 0 → x
  | x, .const 0 => x
  -- 0 + x → x
  | .const 0, x => x
  -- c + x → add(x, c) (normalize constant to right)
  | .const c, x => .add64 x (.const c)
  | _, _ => .add64 a b

partial def foldSub64 {Reg : Type} [DecidableEq Reg]
    (a b : SymExpr Reg) : SymExpr Reg :=
  match a, b with
  -- const - const
  | .const x, .const y => .const (x - y)
  -- sub(x, c1) - c2 → sub(x, c1+c2)
  | .sub64 x (.const c1), .const c2 =>
    let c := c1 + c2
    if c == 0 then x else .sub64 x (.const c)
  -- add(x, c1) - c2 → if c1 ≥ c2: add(x, c1-c2), else sub(x, c2-c1)
  | .add64 x (.const c1), .const c2 =>
    if c1 == c2 then x
    else if c1 > c2 then .add64 x (.const (c1 - c2))
    else .sub64 x (.const (c2 - c1))
  -- x - 0 → x
  | x, .const 0 => x
  | _, _ => .sub64 a b

/-- Simplify: load-after-store resolution + arithmetic constant folding. -/
partial def simplifyLoadStoreExpr {Reg : Type} [DecidableEq Reg] : SymExpr Reg → SymExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (simplifyLoadStoreExpr x)
  | .uext32 x => .uext32 (simplifyLoadStoreExpr x)
  | .sext8to32 x => .sext8to32 (simplifyLoadStoreExpr x)
  | .sext32to64 x => .sext32to64 (simplifyLoadStoreExpr x)
  | .sub32 a b => .sub32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .shl32 a b => .shl32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .add64 a b => foldAdd64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .sub64 a b => foldSub64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .xor64 a b => .xor64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .and64 a b => .and64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .or64 a b => .or64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .shl64 a b => .shl64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .shr64 a b => .shr64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .load w mem addr =>
    let addr' := simplifyLoadStoreExpr addr
    let mem' := simplifyLoadStoreMem mem
    resolveLoadFrom w mem' addr'

/-- Resolve a load from a (simplified) memory term.
    Walks the store chain looking for a matching address. -/
partial def resolveLoadFrom {Reg : Type} [DecidableEq Reg]
    (loadWidth : Width) (mem : SymMem Reg) (loadAddr : SymExpr Reg) : SymExpr Reg :=
  match mem with
  | .base => .load loadWidth .base loadAddr
  | .store storeWidth innerMem storeAddr storeVal =>
    if loadWidth == storeWidth && loadAddr == storeAddr then
      storeVal  -- MATCH: load reads what was just stored
    else
      match (storeAddr, loadAddr) with
      | (.const a, .const b) =>
        if a != b then
          resolveLoadFrom loadWidth innerMem loadAddr  -- different constant addrs, skip store
        else
          .load loadWidth mem loadAddr  -- same const but different width, keep as-is
      -- Non-constant addresses that don't match: can't determine statically,
      -- keep as-is (conservative/sound — may leave loads unresolved)
      | _ => .load loadWidth mem loadAddr

/-- Simplify store chains in a SymMem. -/
partial def simplifyLoadStoreMem {Reg : Type} [DecidableEq Reg] : SymMem Reg → SymMem Reg
  | .base => .base
  | .store w mem addr val =>
    .store w (simplifyLoadStoreMem mem)
            (simplifyLoadStoreExpr addr)
            (simplifyLoadStoreExpr val)
end

/-- Simplify load-after-store patterns in a SymPC. -/
partial def simplifyLoadStorePC {Reg : Type} [DecidableEq Reg] : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq a b => .eq (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .lt a b => .lt (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .le a b => .le (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .and φ ψ => .and (simplifyLoadStorePC φ) (simplifyLoadStorePC ψ)
  | .not φ => .not (simplifyLoadStorePC φ)

/-- Full simplification: load-after-store + constant folding on a branch.
    Returns `none` if the PC is unsatisfiable after simplification. -/
def simplifyBranchFull {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (b : Branch (SymSub Reg) (SymPC Reg)) : Option (Branch (SymSub Reg) (SymPC Reg)) :=
  -- First apply load-after-store to sub and PC
  let simplifiedSub : SymSub Reg := {
    regs := fun r => simplifyLoadStoreExpr (b.sub.regs r)
    mem := simplifyLoadStoreMem b.sub.mem
  }
  let simplifiedPC := simplifyLoadStorePC b.pc
  -- Then apply constant folding
  match SymPC.simplifyConst simplifiedPC with
  | none => none
  | some pc' => some ⟨simplifiedSub, pc'⟩

/-- Zero out non-projected registers (memory savings, safe when projection is closed). -/
def zeroNonProjected {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg] [Hashable Reg]
    (projectedRegs : Std.HashSet Reg) (ip_reg : Reg)
    (b : Branch (SymSub Reg) (SymPC Reg)) : Branch (SymSub Reg) (SymPC Reg) :=
  let projSub : SymSub Reg := {
    regs := fun r =>
      if r == ip_reg then b.sub.regs r
      else if projectedRegs.contains r then b.sub.regs r
      else .const 0
    mem := b.sub.mem  -- keep memory (needed for loads)
  }
  ⟨projSub, b.pc⟩

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
  | .and left _ => extractRipGuard ip_reg left  -- recurse into left-nested ands
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
  -- initSigKey inserted after closedness check determines dedupSubHash
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
  log s!"  data PC regs (direct): [{", ".intercalate (dataPCRegsArr.toList.map toString)}] ({dataPCRegsArr.size} regs, loads={dataPCsHaveLoads})"
  -- Compute transitive closure of register dependency: if a projected register's
  -- body expression references reg R, R must also be projected (since R's value
  -- affects future projected values). Iterate until fixpoint.
  let mut closedRegs := dataPCRegs
  let mut closedNeedsMem := dataPCsHaveLoads
  let mut changed := true
  let mut closureRounds : Nat := 0
  while changed do
    changed := false
    closureRounds := closureRounds + 1
    for b in bodyArr do
      -- Check what each projected register's expression depends on
      let currentRegsArr := closedRegs.toArray
      for r in currentRegsArr do
        let exprRegs := SymExpr.collectRegsHS (b.sub.regs r) {}
        for er in exprRegs do
          unless closedRegs.contains er || er == ip_reg do
            closedRegs := closedRegs.insert er
            changed := true
      -- If we need memory, check what the mem expression depends on
      if closedNeedsMem then
        let memRegs := SymMem.collectRegsHS b.sub.mem {}
        for mr in memRegs do
          unless closedRegs.contains mr || mr == ip_reg do
            closedRegs := closedRegs.insert mr
            changed := true
      -- Check if any projected register's expression involves loads (adds mem dependency)
      unless closedNeedsMem do
        for r in currentRegsArr do
          if SymExpr.hasLoad (b.sub.regs r) then
            closedNeedsMem := true
            changed := true
  let closedRegsArr := closedRegs.toArray
  log s!"  closed projection: [{", ".intercalate (closedRegsArr.toList.map toString)}] ({closedRegsArr.size} regs, loads={closedNeedsMem}, rounds={closureRounds})"
  -- Helper: compute projection hash using the closed register set
  let projHashOf (sub : SymSub Reg) : UInt64 := Id.run do
    let mut h : UInt64 := 0
    for r in closedRegsArr do
      h := mixHash h (hash (sub.regs r))
    if closedNeedsMem then h := mixHash h (hash sub.mem)
    return h
  let dedupSubHash (sub : SymSub Reg) : UInt64 := projHashOf sub
  let initSigKey : SigDedupKey := ⟨dedupSubHash initBranch.sub, initSig⟩
  sigSeen := sigSeen.insert initSigKey
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
        -- Check signature-class dedup (uses projection hash if closed)
        let sig := computePCSignature closure b.pc
        let key : SigDedupKey := ⟨dedupSubHash b.sub, sig⟩
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
      -- Project sub onto closed projection registers
      projectedSubs := projectedSubs.insert (projHashOf b.sub)
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

/-! ## Stratified Fixpoint — Per-Function Summaries

Instead of treating all blocks as one flat dispatch loop, compute fixpoints
bottom-up along the call graph:
1. Leaf functions (next_sym) first — no outgoing calls to other parser functions
2. NT functions (term, sum, test, expr, paren_expr, statement) — call next_sym
   and each other via mutual recursion

At each composition step, when a frontier branch's rip target matches another
function's entry address, compose with that function's current summary instead
of its individual blocks. This prevents cross-function path explosion. -/

/-- A function in the stratified fixpoint. -/
structure FunctionSpec where
  name : String
  entryAddr : UInt64
  blocks : List String  -- raw IRSB strings
  deriving Inhabited

/-- Compose body branches with frontier, but when a body branch's rip target
    matches a function entry, substitute that function's summary branches
    instead of continuing through individual blocks.

    For a body branch B with rip target = function F's entry:
    - Compose B with each branch in F's summary
    - The summary branch has rip = return address (wherever F returns to)
    - Result: caller's pre-call work + F's full behavior + return to caller

    Returns (result, pairsComposed, skipped, dropped, summaryHits). -/
def composeBranchArrayStratified {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg)
    (bodyArr frontierArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg)))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat × Nat × Nat × Nat := Id.run do
  let isa := vexSummaryISA Reg
  -- Build frontier index by rip guard
  let mut frontierByRip : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  let mut frontierNoRip : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  for f in frontierArr do
    match extractRipGuard ip_reg f.pc with
    | some addr =>
      let arr := frontierByRip.getD addr #[]
      frontierByRip := frontierByRip.insert addr (arr.push f)
    | none => frontierNoRip := frontierNoRip.push f
  -- Compose using index + summary substitution
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  let mut summaryHits : Nat := 0
  let totalPairs := bodyArr.size * frontierArr.size
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some target =>
      -- Check if this target is a function entry with a summary
      match summaries.get? target with
      | some summaryBranches =>
        -- Summary substitution: compose this body branch with callee's summary
        summaryHits := summaryHits + 1
        for sb in summaryBranches do
          composed_count := composed_count + 1
          let composed := b.compose isa sb
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' => result := result.push b'
      | none =>
        -- Normal rip-indexed composition
        let compatible := (frontierByRip.getD target #[]) ++ frontierNoRip
        for f in compatible do
          composed_count := composed_count + 1
          let composed := b.compose isa f
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' => result := result.push b'
    | none =>
      -- Can't determine target, fall back to all frontier branches
      for f in frontierArr do
        composed_count := composed_count + 1
        let composed := b.compose isa f
        match simplifyBranch composed with
        | none => dropped := dropped + 1
        | some b' => result := result.push b'
  let skipped := totalPairs - composed_count
  return (result, composed_count, skipped, dropped, summaryHits)

/-- Per-function stabilization with optional initial frontier seeding.
    When initialFrontier is non-empty, those branches are added to the
    initial state (along with skip) instead of starting from skip alone.
    This is used to seed call-expanded results into the frontier without
    putting them in the body (which would cause expression nesting). -/
def computeFunctionStabilization {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg] [ToString Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))))
    (maxIter : Nat) (log : String → IO Unit)
    (initialFrontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]) :
    IO (Option (Nat × Array (Branch (SymSub Reg) (SymPC Reg)))) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  let (closure, ripCount, dataCount) := extractClosure ip_reg bodyArr (dataOnly := true)
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  current := current.insert initBranch
  -- initialFrontier seeded into current AFTER closedness check (needs projection)
  let mut sigSeen : Std.HashSet SigDedupKey := {}
  -- Compute closed projection (same as computeStabilizationHS)
  let mut dataPCRegs : Std.HashSet Reg := {}
  let mut dataPCsHaveLoads := false
  for pc in closure do
    dataPCRegs := SymPC.collectRegsHS pc dataPCRegs
    if SymPC.hasLoad pc then dataPCsHaveLoads := true
  let mut closedRegs := dataPCRegs
  let mut closedNeedsMem := dataPCsHaveLoads
  let mut changed := true
  let mut closureRounds : Nat := 0
  while changed do
    changed := false
    closureRounds := closureRounds + 1
    for b in bodyArr do
      let currentRegsArr := closedRegs.toArray
      for r in currentRegsArr do
        let exprRegs := SymExpr.collectRegsHS (b.sub.regs r) {}
        for er in exprRegs do
          unless closedRegs.contains er || er == ip_reg do
            closedRegs := closedRegs.insert er
            changed := true
      if closedNeedsMem then
        let memRegs := SymMem.collectRegsHS b.sub.mem {}
        for mr in memRegs do
          unless closedRegs.contains mr || mr == ip_reg do
            closedRegs := closedRegs.insert mr
            changed := true
      unless closedNeedsMem do
        for r in currentRegsArr do
          if SymExpr.hasLoad (b.sub.regs r) then
            closedNeedsMem := true
            changed := true
  let closedRegsArr := closedRegs.toArray
  log s!"    closure: rip={ripCount} data={dataCount} proj=[{", ".intercalate (closedRegsArr.toList.map toString)}] ({closedRegsArr.size} regs, rounds={closureRounds})"
  let projHashOf (sub : SymSub Reg) : UInt64 := Id.run do
    let mut h : UInt64 := 0
    for r in closedRegsArr do
      h := mixHash h (hash (sub.regs r))
    if closedNeedsMem then h := mixHash h (hash sub.mem)
    return h
  -- Convergence dedup uses PC signature: which data guard PCs the branch satisfies.
  -- After simplification, branches at different call depths have the same resolved
  -- guard PCs (same token comparisons), so their signatures match even though
  -- rbp/rsp differ. This is the correct convergence criterion from the theory:
  -- K ≤ 2^|closure| bounds the number of distinct PC signature classes.
  -- All distinct branches still go into `current` for the final summary.
  -- Convergence key: PC signature only. Two branches that satisfy the same
  -- set of data guard PCs will produce the same guard PC outcomes in future
  -- iterations, regardless of rbp/rsp/mem differences (call depth).
  let convKey (b : Branch (SymSub Reg) (SymPC Reg)) : UInt64 :=
    hashPCSignature (computePCSignature closure b.pc)
  let mut convSeen : Std.HashSet UInt64 := {}
  convSeen := convSeen.insert (convKey initBranch)
  -- Convergence class representatives for semantic PC equivalence check (Task 1A).
  -- One PC per syntactic-hash class; z3 checks new candidates against all reps.
  let mut convReps : Array (SymPC Reg) := #[initBranch.pc]
  -- Build initial frontier: skip + simplified initial frontier seeds
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[initBranch]
  for b in initialFrontier do
    match simplifyBranchFull b with
    | none => pure ()
    | some sb =>
      let zb := zeroNonProjected closedRegs ip_reg sb
      let key := convKey zb
      unless convSeen.contains key do
        convSeen := convSeen.insert key
        convReps := convReps.push zb.pc
        frontier := frontier.push zb
  -- Seed initial frontier into current set
  for b in frontier do
    current := current.insert b
  log s!"    initial frontier: {frontier.size} branches (skip + {initialFrontier.size} call-expanded)"
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    -- Pure composition: no summary interception, body has no call branches
    let (composed, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr frontier
    -- Simplify: load-after-store + constant folding + zero non-projected
    let mut simplified : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut droppedSimplify : Nat := 0
    for b in composed do
      match simplifyBranchFull b with
      | none => droppedSimplify := droppedSimplify + 1
      | some sb => simplified := simplified.push (zeroNonProjected closedRegs ip_reg sb)
    let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut dupes : Nat := 0
    let mut projCollapsed : Nat := 0
    -- Phase 1: exact-match dedup; collect syntactically-new conv-key candidates
    let mut syntacticNewCands : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for b in simplified do
      if current.contains b then
        dupes := dupes + 1
      else
        current := current.insert b  -- ALL distinct branches kept for summary
        let key := convKey b
        if convSeen.contains key then
          projCollapsed := projCollapsed + 1
        else
          syntacticNewCands := syntacticNewCands.push b
    -- Phase 2: semantic equivalence check via z3 for syntactically-new candidates.
    -- Query: (P_new ∧ ¬P_rep) ∨ (P_rep ∧ ¬P_new) UNSAT ⟺ P_new ≡ P_rep.
    -- Batch all (cand_i, rep_j) pairs into one z3 invocation using push/pop.
    let mut semCollapsed : Nat := 0
    if syntacticNewCands.size > 0 && convReps.size > 0 then
      let mut convPairs : Array (SymPC Reg × SymPC Reg) := #[]
      let mut convPairCandIdx : Array Nat := #[]
      let mut ci : Nat := 0
      for cand in syntacticNewCands do
        for rep in convReps do
          convPairs := convPairs.push (cand.pc, rep)
          convPairCandIdx := convPairCandIdx.push ci
        ci := ci + 1
      -- Collect SMT variable names across all queries
      let mut convRegNames : Std.HashSet String := {}
      let mut convNeedsMem := false
      for (cp, rp) in convPairs do
        convRegNames := SymPC.collectRegNames cp convRegNames
        convRegNames := SymPC.collectRegNames rp convRegNames
        if SymPC.hasLoad cp || SymPC.hasLoad rp then convNeedsMem := true
      -- Generate SMT-LIB2 script
      let mut convScript := smtPreamble convRegNames convNeedsMem
      for (cp, rp) in convPairs do
        convScript := convScript ++ "(push)\n"
        convScript := convScript ++ s!"(assert (or (and {SymPC.toSMTLib cp} (not {SymPC.toSMTLib rp})) (and {SymPC.toSMTLib rp} (not {SymPC.toSMTLib cp}))))\n"
        convScript := convScript ++ "(check-sat)\n"
        convScript := convScript ++ "(pop)\n"
      convScript := convScript ++ "(exit)\n"
      let convTmpFile : System.FilePath := ".lake/smt_conv_equiv.smt2"
      IO.FS.writeFile convTmpFile convScript
      let convZ3 ← IO.Process.output { cmd := "z3", args := #[convTmpFile.toString] }
      let convLines := convZ3.stdout.splitOn "\n" |>.filter (· != "")
      -- Find candidates semantically equivalent to at least one rep (unsat = equiv)
      let mut convEquivCands : Std.HashSet Nat := {}
      for i in [:convPairs.size] do
        if h : i < convLines.length then
          if convLines[i] == "unsat" then
            if h2 : i < convPairCandIdx.size then
              convEquivCands := convEquivCands.insert convPairCandIdx[i]
      log s!"    z3 conv equiv: {convPairs.size} queries → {convEquivCands.size} sem-collapsed"
      -- Promote candidates: collapsed if equiv to any rep, else new conv class
      let mut ci2 : Nat := 0
      for cand in syntacticNewCands do
        if convEquivCands.contains ci2 then
          semCollapsed := semCollapsed + 1
        else
          convSeen := convSeen.insert (convKey cand)
          convReps := convReps.push cand.pc
          newBranches := newBranches.push cand
        ci2 := ci2 + 1
    else
      -- No reps yet or no candidates: all syntactically-new candidates are new classes
      for cand in syntacticNewCands do
        convSeen := convSeen.insert (convKey cand)
        convReps := convReps.push cand.pc
        newBranches := newBranches.push cand
    let t_end ← IO.monoMsNow
    log s!"    K={k}: |S|={current.size} |new|={newBranches.size} |conv_classes|={convSeen.size} |conv_reps|={convReps.size} pairs={pairsComposed} skipped={skipped} dropped={dropped}+{droppedSimplify} dupes={dupes} conv_collapsed={projCollapsed}+{semCollapsed}sem {t_end - t_start}ms"
    -- Diagnostic: dump expression details for first few iterations
    if k ≤ 4 && newBranches.size > 0 then
      -- Aggregate stats across all new branches
      let mut totalNodes : Nat := 0
      let mut totalUnresolved : Nat := 0
      let mut maxNodes : Nat := 0
      for b in newBranches do
        let mut bNodes : Nat := 0
        let mut bUnresolved : Nat := 0
        for r in closedRegsArr do
          let e := b.sub.regs r
          bNodes := bNodes + exprNodeCount e
          bUnresolved := bUnresolved + exprUnresolvedLoads e
        bNodes := bNodes + memNodeCount b.sub.mem
        totalNodes := totalNodes + bNodes
        totalUnresolved := totalUnresolved + bUnresolved
        if bNodes > maxNodes then maxNodes := bNodes
      log s!"      expr stats: total_nodes={totalNodes} avg={totalNodes / newBranches.size} max={maxNodes} unresolved_loads={totalUnresolved}"
      -- Dump first 2 new branches in detail
      let mut dumpIdx : Nat := 0
      for b in newBranches do
        if dumpIdx < 2 then
          let mut regSummaries : List String := []
          for r in closedRegsArr do
            let e := b.sub.regs r
            regSummaries := regSummaries ++ [s!"{r}={exprSummary e 3}[{exprNodeCount e}n,{exprUnresolvedLoads e}ul]"]
          log s!"      branch[{dumpIdx}]: {", ".intercalate regSummaries} mem[{memNodeCount b.sub.mem}n]"
          dumpIdx := dumpIdx + 1
    if newBranches.size == 0 then
      -- Collect all branches as array for the summary
      let summaryArr := current.toArray
      -- Task 1B: Closure closedness verification.
      -- For each branch b in summaryArr and each data guard PC phi in closure:
      --   lifted = substSymPC b.sub phi  (the pc_lift from VexSummary/VexCompTree)
      --   simplified = simplifyLoadStorePC lifted |> SymPC.simplifyConst
      --   check: simplified ≡ some phi_j in closure, or trivially true/false
      do
        log s!"    [closedness] checking {summaryArr.size} branches × {closure.size} guards..."
        let mut trivClosedPairs : Nat := 0   -- simplified to true/false or syntactic match
        let mut needsZ3Pairs : Nat := 0      -- require z3 semantic check
        -- z3 query data: for each lifted PC that fails syntactic check,
        -- compare against each phi_j in closure
        let mut closedQueryPairs : Array (SymPC Reg × SymPC Reg) := #[]
        let mut closedQueryLiftedIdx : Array Nat := #[]
        let mut liftedNeedingCheck : Array Nat := #[]  -- globalIdx of non-trivial lifted PCs
        let mut globalIdx : Nat := 0
        for b in summaryArr do
          for phi in closure do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePC lifted
            match SymPC.simplifyConst liftedSimplified with
            | none =>
              trivClosedPairs := trivClosedPairs + 1  -- false: unsatisfiable, trivially closed
            | some .true =>
              trivClosedPairs := trivClosedPairs + 1  -- true: trivially closed
            | some pc' =>
              -- Fast-path: syntactic match against closure
              let inClosure := pc' == .true || closure.any (fun phi_j => phi_j == pc')
              if inClosure then
                trivClosedPairs := trivClosedPairs + 1
              else
                -- Need z3 check: is pc' semantically equiv to some phi_j?
                for phi_j in closure do
                  closedQueryPairs := closedQueryPairs.push (pc', phi_j)
                  closedQueryLiftedIdx := closedQueryLiftedIdx.push globalIdx
                liftedNeedingCheck := liftedNeedingCheck.push globalIdx
                needsZ3Pairs := needsZ3Pairs + 1
            globalIdx := globalIdx + 1
        log s!"    [closedness] trivial={trivClosedPairs}/{globalIdx} z3_candidates={needsZ3Pairs}"
        -- Run z3 semantic check for non-trivial lifted PCs
        let mut closednessViolations : Nat := 0
        if closedQueryPairs.size > 0 then
          let mut closedRegNames : Std.HashSet String := {}
          let mut closedNeedsMem2 := false
          for (cp, rp) in closedQueryPairs do
            closedRegNames := SymPC.collectRegNames cp closedRegNames
            closedRegNames := SymPC.collectRegNames rp closedRegNames
            if SymPC.hasLoad cp || SymPC.hasLoad rp then closedNeedsMem2 := true
          let mut closedScript := smtPreamble closedRegNames closedNeedsMem2
          for (cp, rp) in closedQueryPairs do
            closedScript := closedScript ++ "(push)\n"
            closedScript := closedScript ++ s!"(assert (or (and {SymPC.toSMTLib cp} (not {SymPC.toSMTLib rp})) (and {SymPC.toSMTLib rp} (not {SymPC.toSMTLib cp}))))\n"
            closedScript := closedScript ++ "(check-sat)\n"
            closedScript := closedScript ++ "(pop)\n"
          closedScript := closedScript ++ "(exit)\n"
          let closedTmpFile : System.FilePath := ".lake/smt_closedness.smt2"
          IO.FS.writeFile closedTmpFile closedScript
          let closedZ3 ← IO.Process.output { cmd := "z3", args := #[closedTmpFile.toString] }
          let closedLines := closedZ3.stdout.splitOn "\n" |>.filter (· != "")
          -- Collect lifted PC indices that are semantically closed (unsat = equiv to some phi_j)
          let mut closedByZ3 : Std.HashSet Nat := {}
          for i in [:closedQueryPairs.size] do
            if h : i < closedLines.length then
              if closedLines[i] == "unsat" then
                if h2 : i < closedQueryLiftedIdx.size then
                  closedByZ3 := closedByZ3.insert closedQueryLiftedIdx[i]
          -- Violations: lifted PCs not closed by z3
          for gIdx in liftedNeedingCheck do
            unless closedByZ3.contains gIdx do
              closednessViolations := closednessViolations + 1
          log s!"    [closedness] z3: {closedQueryPairs.size} queries, {closedByZ3.size} closed, {closednessViolations} violations"
        let isClosed := closednessViolations == 0
        log s!"    [closedness] closure closed: {if isClosed then "YES" else "NO"}, violations={closednessViolations}"
      return some (k, summaryArr)
    frontier := newBranches
  return none

/-- Split body branches into non-call (kept in body) and call-expanded
    (seeded into initial frontier).

    For each body branch B:
    - If B's rip target matches a function entry with a summary:
      Compose B with each summary branch → add to callResults (initial frontier)
      B is REMOVED from the body.
    - Otherwise: B stays in the body for iterative composition.

    This prevents re-expansion: summary results are in the initial frontier,
    and the body only contains the function's own non-call blocks. Each
    iteration composes non-call blocks with frontier — no expression nesting. -/
def splitBodyAndExpandCalls {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg)
    (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg)))) :
    (Array (Branch (SymSub Reg) (SymPC Reg))  -- nonCallBody (for iterative composition)
    × Array (Branch (SymSub Reg) (SymPC Reg))  -- callResults (initial frontier seed)
    × Nat × Nat × Nat) := Id.run do  -- callsExpanded, branchesAdded, dropped
  let isa := vexSummaryISA Reg
  let mut nonCallBody : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut callResults : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut callsExpanded : Nat := 0
  let mut branchesAdded : Nat := 0
  let mut dropped : Nat := 0
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some target =>
      match summaries.get? target with
      | some summaryBranches =>
        callsExpanded := callsExpanded + 1
        for sb in summaryBranches do
          let composed := b.compose isa sb
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' =>
            callResults := callResults.push b'
            branchesAdded := branchesAdded + 1
      | none =>
        nonCallBody := nonCallBody.push b
    | none =>
      nonCallBody := nonCallBody.push b
  return (nonCallBody, callResults, callsExpanded, branchesAdded, dropped)

def stratifiedFixpoint
    (functions : Array FunctionSpec)
    (log : String → IO Unit) :
    IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  -- Parse all function blocks into raw body arrays
  let mut funcBlocks : Array (String × Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := #[]
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error e =>
      log s!"  PARSE ERROR for {func.name}: {e}"
      return {}
    | .ok pairs =>
      let body := flatBodyDenot ip_reg pairs
      let bodyArr := finsetToArray body
      funcBlocks := funcBlocks.push (func.name, bodyArr)
      log s!"  {func.name} @ 0x{String.mk (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches"
  -- Phase 1: Compute leaf function (next_sym) fixpoint — no summaries needed
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  log s!"\n--- Phase 1: Leaf function (next_sym) ---"
  let t0 ← IO.monoMsNow
  let (nextSymName, nextSymBody) := funcBlocks[0]!
  -- Use computeFunctionStabilization directly (returns branch array as summary).
  -- Don't double-run with computeStabilizationHS — that keeps two copies of deeply-nested
  -- symbolic branches alive simultaneously, causing OOM.
  match ← computeFunctionStabilization ip_reg nextSymBody {} 200 log with
  | some (k, summaryArr) =>
    let t1 ← IO.monoMsNow
    summaries := summaries.insert functions[0]!.entryAddr summaryArr
    log s!"  {nextSymName}: converged at K={k}, {summaryArr.size} summary branches, {t1 - t0}ms"
  | none =>
    log s!"  {nextSymName}: DID NOT CONVERGE"
    return {}
  -- Phase 2: Iterate NT function summaries to fixpoint
  -- At each outer round, for each NT function:
  --   1. Split body into non-call blocks + call-expanded results (via splitBodyAndExpandCalls)
  --   2. Run stabilization on non-call body, seeding call results as initial frontier
  --   3. The converged set = new function summary
  -- Key: non-call body never contains summary-expanded branches, preventing expression nesting
  log s!"\n--- Phase 2: NT functions (mutual recursion) ---"
  -- Initialize NT summaries as empty
  for i in [1:functions.size] do
    summaries := summaries.insert functions[i]!.entryAddr #[]
  let mut outerRound : Nat := 0
  let mut outerChanged := true
  while outerChanged do
    outerChanged := false
    outerRound := outerRound + 1
    log s!"\n  === Outer round {outerRound} ==="
    for i in [1:functions.size] do
      let func := functions[i]!
      let (fname, rawBody) := funcBlocks[i]!
      let t0 ← IO.monoMsNow
      -- Step 1: Split body into non-call blocks + call-expanded results
      let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
        splitBodyAndExpandCalls ip_reg rawBody summaries
      log s!"    {fname}: split body {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, {branchesAdded} branches, {droppedExp} dropped)"
      -- Step 2: Run stabilization on non-call body, seeding call results as initial frontier
      let oldSummary := summaries.getD func.entryAddr #[]
      match ← computeFunctionStabilization ip_reg nonCallBody {} 30 log (initialFrontier := callResults) with
      | some (k, newSummary) =>
        let t1 ← IO.monoMsNow
        if newSummary.size != oldSummary.size then
          outerChanged := true
          summaries := summaries.insert func.entryAddr newSummary
          log s!"  {fname}: K={k}, {newSummary.size} branches (was {oldSummary.size}), {t1 - t0}ms [CHANGED]"
        else
          log s!"  {fname}: K={k}, {newSummary.size} branches (stable), {t1 - t0}ms"
      | none =>
        log s!"  {fname}: DID NOT CONVERGE"
        return {}
  log s!"\n=== Stratified fixpoint complete after {outerRound} outer rounds ==="
  for i in [:functions.size] do
    let func := functions[i]!
    let summary := summaries.getD func.entryAddr #[]
    log s!"  {func.name}: {summary.size} branches"
  return summaries

/-! ## DFA & CFG Extraction -/

/-- Strip rip-guard conjuncts from a PC, returning only the data guard. -/
def stripRipGuards {Reg : Type} [BEq Reg] (ip_reg : Reg) (pc : SymPC Reg) : SymPC Reg :=
  let cs := SymPC.conjuncts pc |>.filter fun c => match c with
    | .eq (.reg r) (.const _) => !(r == ip_reg)
    | _ => true
  match cs with
  | [] => .true
  | c :: rest => rest.foldl .and c

/-- Pretty-print a SymExpr concisely. -/
partial def ppExpr : SymExpr Amd64Reg → String
  | .const v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then s!"'{Char.ofNat n}'"
    else s!"{n}"
  | .reg r => toString r
  | .add64 a b => s!"({ppExpr a}+{ppExpr b})"
  | .sub64 a b => s!"({ppExpr a}-{ppExpr b})"
  | .and64 a b => s!"({ppExpr a}&{ppExpr b})"
  | .or64  a b => s!"({ppExpr a}|{ppExpr b})"
  | .xor64 a b => s!"({ppExpr a}^{ppExpr b})"
  | .shr64 a b => s!"({ppExpr a}>>{ppExpr b})"
  | .shl64 a b => s!"({ppExpr a}<<{ppExpr b})"
  | .low32 e   => s!"lo32({ppExpr e})"
  | .uext32 e  => s!"zx32({ppExpr e})"
  | .sext32to64 e => s!"sx32({ppExpr e})"
  | _ => "..."

/-- Pretty-print a SymPC atom as a character condition on rax. -/
partial def ppCharCond (rax : Amd64Reg) : SymPC Amd64Reg → String
  | .eq (.reg r) (.const c) =>
    if r == rax then
      let n := c.toNat
      if n ≥ 32 && n ≤ 126 then s!"rax=='{Char.ofNat n}'"
      else s!"rax=={n}"
    else s!"{r}=={ppExpr (.const c)}"
  | .eq l r => s!"{ppExpr l}=={ppExpr r}"
  | .le (.const lo) (.reg r) =>
    if r == rax then s!"rax>={lo.toNat}" else s!"{lo.toNat}<={r}"
  | .le (.reg r) (.const hi) =>
    if r == rax then s!"rax<={hi.toNat}" else s!"{r}<={hi.toNat}"
  | .le l r => s!"{ppExpr l}<={ppExpr r}"
  | .lt (.const lo) (.reg r) =>
    if r == rax then s!"rax>{lo.toNat}" else s!"{lo.toNat}<{r}"
  | .lt (.reg r) (.const hi) =>
    if r == rax then s!"rax<{hi.toNat}" else s!"{r}<{hi.toNat}"
  | .lt l r => s!"{ppExpr l}<{ppExpr r}"
  | .not inner => "NOT(" ++ ppCharCond rax inner ++ ")"
  | .true => "true"
  | _ => "<cond>"

/-- Format a data guard PC (non-rip conjuncts) as a human-readable string. -/
def describeDataGuard (rax : Amd64Reg) (pc : SymPC Amd64Reg) : String :=
  let cs := SymPC.conjuncts pc
  match cs with
  | [.true] => "*"
  | _ => " & ".intercalate (cs.map (ppCharCond rax))

/-- Format a UInt64 as a hex address. -/
def hexAddr (a : UInt64) : String :=
  s!"0x{String.mk (Nat.toDigits 16 a.toNat)}"

/-- Print DFA transition table from next_sym body branches (single-step transitions). -/
def printDFATable (log : String → IO Unit)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) : IO Unit := do
  let ip_reg := Amd64Reg.rip
  let rax_reg := Amd64Reg.rax
  let mut trans : Array (UInt64 × SymPC Amd64Reg × UInt64) := #[]
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
    | some src, some tgt =>
      trans := trans.push (src, stripRipGuards ip_reg b.pc, tgt)
    | _, _ => pure ()
  log s!"\n=== DFA Transition Table (next_sym, {trans.size} single-step transitions) ==="
  let mut bySource : Std.HashMap UInt64 (Array (SymPC Amd64Reg × UInt64)) := {}
  let mut allStates : Std.HashSet UInt64 := {}
  for (src, guard, tgt) in trans do
    let arr := bySource.getD src #[]
    bySource := bySource.insert src (arr.push (guard, tgt))
    allStates := allStates.insert src
    allStates := allStates.insert tgt
  log s!"  States: {allStates.size}, Source states: {bySource.size}"
  for (src, edges) in bySource.toArray do
    log s!"  State {hexAddr src}:"
    for (guard, tgt) in edges do
      log s!"    [{describeDataGuard rax_reg guard}] -> {hexAddr tgt}"

/-! ## Production Extraction via Body CFG -/

/-- Check if a SymExpr references the rsp register (for detecting call return-address stores). -/
partial def exprUsesRSP : SymExpr Amd64Reg → Bool
  | .reg .rsp => true
  | .add64 a b | .sub64 a b => exprUsesRSP a || exprUsesRSP b
  | .load _ _ addr => exprUsesRSP addr
  | _ => false

/-- Extract the constant return address pushed by a call instruction at [rsp - k]. -/
partial def extractCallReturn (mem : SymMem Amd64Reg) : Option UInt64 :=
  match mem with
  | .base => none
  | .store _ inner addr (.const v) =>
    if exprUsesRSP addr then some v else extractCallReturn inner
  | .store _ inner _ _ => extractCallReturn inner

/-- Strip sign-extension / low-extract wrappers and +offset to reach a raw constant.
    Used to decode the character constants inside VEX-style signed-comparison expressions
    (e.g. sx32(lo32(lo32(const '/')))+2^63  →  '/').
    Returns Some v only if v is a printable ASCII char (32..126). -/
partial def stripToCharConst : SymExpr Amd64Reg → Option UInt64
  | .const v => if v.toNat ≥ 32 && v.toNat ≤ 126 then some v else none
  | .low32 inner | .uext32 inner | .sext32to64 inner => stripToCharConst inner
  | .add64 a b => stripToCharConst a <|> stripToCharConst b
  | _ => none

/-- Try to extract a printable ASCII character from an expression (even if wrapped). -/
def extractCharConstFromExpr (e : SymExpr Amd64Reg) : Option Char :=
  (stripToCharConst e).bind fun v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then some (Char.ofNat n) else none

/-- Describe the expected token at a next_sym call site, given the data guard PC.
    Extracts character constants and infers token class (id, int, or specific char). -/
def describeCallSiteToken (guard : SymPC Amd64Reg) : String :=
  let cs := SymPC.conjuncts guard
  if cs == [.true] then "token"
  else
    -- Priority 1: exact equality (specific character)
    let eqChar := cs.findSome? fun c => match c with
      | .eq l r => extractCharConstFromExpr l <|> extractCharConstFromExpr r
      | _ => none
    match eqChar with
    | some ch => s!"'{ch}'"
    | none =>
      -- Priority 2: range check → infer digit / letter class
      let loBounds := cs.filterMap fun c => match c with
        | .le l _ | .lt l _ => extractCharConstFromExpr l
        | _ => none
      let hiBounds := cs.filterMap fun c => match c with
        | .le _ r | .lt _ r => extractCharConstFromExpr r
        | _ => none
      match loBounds, hiBounds with
      | lo :: _, hi :: _ =>
        if lo == '/' || lo == '0' then "int"
        else if lo == '`' || lo == 'a' then "id"
        else s!"[{lo}..{hi}]"
      | _, hi :: _ => s!"..{hi}"
      | lo :: _, _ => s!"{lo}.."
      | _, _ => "token"

/-- Annotated body CFG: src_addr → [(dataGuard, tgt_addr, returnAddr?)] -/
abbrev AnnotatedCFG := Std.HashMap UInt64 (Array (SymPC Amd64Reg × UInt64 × Option UInt64))

/-- Build annotated body CFG from raw body branches. -/
def buildAnnotatedBodyCFG (ip_reg : Amd64Reg)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) :
    AnnotatedCFG × Std.HashSet UInt64 := Id.run do
  let mut cfg : AnnotatedCFG := {}
  let mut blocks : Std.HashSet UInt64 := {}
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
    | some src, some tgt =>
      blocks := blocks.insert src
      let guard := stripRipGuards ip_reg b.pc
      let ret := extractCallReturn b.sub.mem
      let edges := cfg.getD src #[]
      cfg := cfg.insert src (edges.push (guard, tgt, ret))
    | _, _ => pure ()
  return (cfg, blocks)

/-- DFS through body CFG collecting ordered call sequences as productions.
    Each external call (to next_sym or another NT) becomes one production symbol.
    The return address in memory is used to find the continuation after each call. -/
partial def dfsExtractProds
    (cur : UInt64)
    (steps : Array String)
    (cfg : AnnotatedCFG)
    (blocks : Std.HashSet UInt64)
    (funcEntries : Std.HashMap UInt64 String)
    (visited : Std.HashSet UInt64)
    (depth : Nat) :
    Array (Array String) := Id.run do
  if depth > 60 || visited.contains cur then return #[steps]
  let visited' := visited.insert cur
  let edges := cfg.getD cur #[]
  if edges.isEmpty then
    return if steps.isEmpty then #[] else #[steps]
  let mut allPaths : Array (Array String) := #[]
  for (guard, tgt, retOpt) in edges do
    match funcEntries.get? tgt with
    | some "_exit" =>
      -- Error/abort path: drop this alternative (do not record, do not continue)
      pure ()
    | some callee =>
      -- External call: record as a production symbol
      let sym := if callee == "next_sym"
                 then describeCallSiteToken guard
                 else callee
      let steps' := steps.push sym
      match retOpt with
      | some ret =>
        if blocks.contains ret then
          allPaths := allPaths.append
            (dfsExtractProds ret steps' cfg blocks funcEntries visited' (depth + 1))
        else
          allPaths := allPaths.push steps'  -- call is at function tail
      | none =>
        allPaths := allPaths.push steps'  -- can't determine continuation
    | none =>
      -- Internal transition, known-unknown helper, or function exit
      if blocks.contains tgt then
        -- Internal transition within this function: recurse without recording a step
        allPaths := allPaths.append
          (dfsExtractProds tgt steps cfg blocks funcEntries visited' (depth + 1))
      else
        -- External call to unknown helper (e.g. a helper like isdigit called before next_sym).
        -- Follow the return address to find the continuation (the helper is transparent).
        match retOpt with
        | some ret =>
          if blocks.contains ret then
            allPaths := allPaths.append
              (dfsExtractProds ret steps cfg blocks funcEntries visited' (depth + 1))
          else if !steps.isEmpty then
            allPaths := allPaths.push steps  -- tail call to unknown, end path
        | none =>
          if !steps.isEmpty then
            allPaths := allPaths.push steps  -- true exit
  return allPaths

/-- Golden grammar productions (from golden_grammar_tinyc.json).
    Each entry: (NT name, list of RHS alternatives as symbol sequences). -/
def goldenProds : Std.HashMap String (List (List String)) :=
  ({} : Std.HashMap String (List (List String)))
    |>.insert "term"       [["id"], ["int"], ["paren_expr"]]
    |>.insert "sum"        [["term"], ["term", "'+' term ...loop"]]
    |>.insert "test"       [["sum"], ["sum", "'<'", "sum"]]
    |>.insert "expr"       [["test"], ["id", "'='", "expr"]]
    |>.insert "paren_expr" [["'('", "expr", "')'"]]
    |>.insert "statement"  [
        ["'('", "expr", "')'", "statement"],
        ["'('", "expr", "')'", "statement", "'else'", "statement"],
        ["statement", "'while'", "'('", "expr", "')'", "';'"],
        ["expr", "';'"],
        ["'{'"],
        ["'}'"],
        ["';'"]
      ]

/-- BFS to find all blocks reachable from entry, following:
    - internal transitions (tgt in blocks)
    - return continuations after external calls (retOpt if tgt not in blocks) -/
def cfgReachable (entry : UInt64) (cfg : AnnotatedCFG) (blocks : Std.HashSet UInt64)
    (funcEntries : Std.HashMap UInt64 String) :
    Std.HashSet UInt64 := Id.run do
  let mut visited : Std.HashSet UInt64 := {}
  let mut queue : Array UInt64 := #[entry]
  while !queue.isEmpty do
    let cur := queue.back!
    queue := queue.pop
    if visited.contains cur then pure ()
    else
      visited := visited.insert cur
      for (_, tgt, retOpt) in cfg.getD cur #[] do
        if blocks.contains tgt && !visited.contains tgt then
          queue := queue.push tgt   -- internal transition
        else
          -- external call: follow return continuation
          match retOpt with
          | some ret =>
            if blocks.contains ret && !visited.contains ret then
              queue := queue.push ret
          | none => pure ()
  return visited

/-- Extract productions for one NT function and print them with golden comparison. -/
def printFunctionProductions (log : String → IO Unit)
    (funcName : String) (entryAddr : UInt64)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String) : IO Unit := do
  let ip_reg := Amd64Reg.rip
  let (cfg, blocks) := buildAnnotatedBodyCFG ip_reg bodyArr
  let rawPaths := dfsExtractProds entryAddr #[] cfg blocks funcEntries {} 0
  -- Also explore orphan loop-body blocks (not reachable from entry via internal CFG).
  -- For NT calls (not next_sym) in orphan blocks, start DFS from the return continuation
  -- with the callee as the first step. This captures iterative loop alternatives like
  -- sum's "term '+' term" without spurious fragments from next_sym return sites.
  let reachable := cfgReachable entryAddr cfg blocks funcEntries
  let mut orphanPaths : Array (Array String) := #[]
  for (src, edges) in cfg.toArray do
    if reachable.contains src then pure ()  -- skip reachable blocks
    else
      for (_guard, tgt, retOpt) in edges do
        match funcEntries.get? tgt with
        | some "_exit" | some "next_sym" => pure ()  -- skip exit and terminals
        | some callee =>
          match retOpt with
          | some ret =>
            if blocks.contains ret then
              -- Start DFS from NT call's return continuation, with callee as first step
              orphanPaths := orphanPaths.append
                (dfsExtractProds ret #[callee] cfg blocks funcEntries {} 0)
          | none => pure ()
        | none => pure ()
  -- Deduplicate
  let mut seen : Std.HashSet String := {}
  let mut unique : Array (Array String) := #[]
  for p in rawPaths.append orphanPaths do
    let key := " ".intercalate p.toList
    if !seen.contains key then
      seen := seen.insert key
      unique := unique.push p
  let golden := goldenProds.getD funcName []
  log s!"\n{funcName}: {unique.size} extracted productions (golden has {golden.length} alternatives)"
  for prod in unique do
    let rhs := if prod.isEmpty then "ε" else " ".intercalate prod.toList
    log s!"  {funcName} -> {rhs}"
  if !golden.isEmpty then
    log s!"  -- Golden:"
    for g in golden do
      log s!"  -- {funcName} -> {" ".intercalate g}"

/-- Print productions for all NT functions. -/
def printGrammarProductions (log : String → IO Unit)
    (functions : Array FunctionSpec)
    (funcEntries : Std.HashMap UInt64 String) : IO Unit := do
  log "\n=== Grammar Productions (Body CFG DFS) ==="
  let ip_reg := Amd64Reg.rip
  for i in [1:functions.size] do
    let func := functions[i]!
    match parseBlocksWithAddresses func.blocks with
    | .error e => log s!"  Parse error for {func.name}: {e}"
    | .ok pairs =>
      let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
      printFunctionProductions log func.name func.entryAddr bodyArr funcEntries

/-- Extract CFG info from body branches: count next_sym calls and collect called NT names. -/
def extractBodyCFG (ip_reg : Amd64Reg)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String) : Nat × Std.HashSet String := Id.run do
  let mut nsCount : Nat := 0
  let mut calledNTs : Std.HashSet String := {}
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some tgt =>
      match funcEntries.get? tgt with
      | some name =>
        if name == "next_sym" then nsCount := nsCount + 1
        else calledNTs := calledNTs.insert name
      | none => pure ()
    | none => pure ()
  return (nsCount, calledNTs)

/-! ## Golden Grammar Comparison -/

/-- Expected callee NTs for each NT function (from golden_grammar_tinyc.json). -/
def goldenCallees : Std.HashMap String (List String) :=
  ({} : Std.HashMap String (List String))
    |>.insert "term"       ["paren_expr"]
    |>.insert "sum"        ["term"]  -- iterative impl: loop body, no recursive call
    |>.insert "test"       ["sum"]
    |>.insert "expr"       ["test", "expr"]
    |>.insert "paren_expr" ["expr"]
    |>.insert "statement"  ["paren_expr", "statement", "expr"]

/-- Expected: does each NT call next_sym (consume tokens)? -/
def goldenCallsNextSym : Std.HashMap String Bool :=
  ({} : Std.HashMap String Bool)
    |>.insert "term"       true   -- reads id or int tokens
    |>.insert "sum"        true   -- reads + or - token
    |>.insert "test"       true   -- reads < token
    |>.insert "expr"       true   -- reads = token (assignment alt)
    |>.insert "paren_expr" true   -- reads ( and ) tokens
    |>.insert "statement"  true   -- reads if/while/do/;/{/} tokens

/-- Compare extracted CFG with golden grammar and print results. -/
def printGrammarComparison (log : String → IO Unit)
    (extractedCFG : Std.HashMap String (Nat × List String)) : IO Unit := do
  log "\n=== Grammar Comparison (Extracted vs Golden) ==="
  let ntNames := ["term", "sum", "test", "expr", "paren_expr", "statement"]
  for name in ntNames do
    let (nsCount, calledNTs) := extractedCFG.getD name (0, [])
    let expectedCallees := goldenCallees.getD name []
    let expectedNS := goldenCallsNextSym.getD name false
    let callsNS := nsCount != 0
    -- Check if extracted callees contain all expected ones
    let calledSet : Std.HashSet String := calledNTs.foldl (fun s x => s.insert x) {}
    let missing := expectedCallees.filter (fun e => !calledSet.contains e)
    let ntOk := missing.isEmpty
    let nsOk := callsNS == expectedNS
    let status := if ntOk && nsOk then "OK" else "MISMATCH"
    let calledStr := ", ".intercalate calledNTs
    let expStr := ", ".intercalate expectedCallees
    let missingStr := if missing.isEmpty then "" else " MISSING=[" ++ ", ".intercalate missing ++ "]"
    log s!"  [{status}] {name}: next_sym={callsNS}(exp={expectedNS}) calls=[{calledStr}] exp=[{expStr}]{missingStr}"

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
  -- Stratified fixpoint: per-function summaries
  log "=== Stratified Dispatch Loop Stabilization ==="
  -- Use nextSymBlocks.take 55 for the leaf portion of next_sym (blocks 56-60
  -- in nextSymBlocks are calling-convention blocks from other functions that
  -- were included before proper per-function extraction). The 55 leaf blocks
  -- converge to 414 branches with a 3-register projection {rax, rbp, rsp}.
  -- NT function block lists come from parser_nt_blocks.json extraction.
  let functions : Array FunctionSpec := #[
    ⟨"next_sym",    0x40006f, nextSymBlocks.take 55⟩,
    ⟨"term",        0x400427, termBlocks⟩,
    ⟨"sum",         0x4004be, sumBlocks⟩,
    ⟨"test",        0x400551, testBlocks⟩,
    ⟨"expr",        0x4005bd, exprBlocks⟩,
    ⟨"paren_expr",  0x40064d, paren_exprBlocks⟩,
    ⟨"statement",   0x4006b1, statementBlocks⟩
  ]
  let _summaries ← stratifiedFixpoint functions log
  -- Task 2B: DFA extraction from next_sym body branches (raw, before stabilization)
  let ip_reg := Amd64Reg.rip
  match parseBlocksWithAddresses (nextSymBlocks.take 55) with
  | .error e => log s!"DFA parse error: {e}"
  | .ok pairs =>
    let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
    printDFATable log bodyArr
  -- Task 2C: CFG extraction from NT body branches
  let funcEntries : Std.HashMap UInt64 String :=
    ({} : Std.HashMap UInt64 String)
      |>.insert 0x40006f "next_sym"
      |>.insert 0x400427 "term"
      |>.insert 0x4004be "sum"
      |>.insert 0x400551 "test"
      |>.insert 0x4005bd "expr"
      |>.insert 0x40064d "paren_expr"
      |>.insert 0x4006b1 "statement"
      |>.insert 0x400000 "_exit"
  log "\n=== CFG Extraction (NT body branches) ==="
  let mut extractedCFG : Std.HashMap String (Nat × List String) := {}
  for i in [1:functions.size] do
    let func := functions[i]!
    match parseBlocksWithAddresses func.blocks with
    | .error e => log s!"  Parse error for {func.name}: {e}"
    | .ok pairs =>
      let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
      let (nsCount, calledNTsHS) := extractBodyCFG ip_reg bodyArr funcEntries
      let calledList := calledNTsHS.toArray.toList
      extractedCFG := extractedCFG.insert func.name (nsCount, calledList)
      log s!"  {func.name}: next_sym_calls={nsCount} NTs=[{", ".intercalate calledList}]"
  -- Task 2D: Compare with golden grammar (call graph)
  printGrammarComparison log extractedCFG
  -- Task 2D (productions): extract actual grammar productions via body CFG DFS
  printGrammarProductions log functions funcEntries
