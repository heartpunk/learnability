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

/-! ## PC Expression Canonicalization (Kuznetsov et al. 2012)

Normalizes SymExpr/SymPC so that syntactically different but semantically
equivalent expressions hash identically. Applied in `computePCSignature`
before conjunct comparison, strengthening the syntactic fast-path so z3
is only invoked for genuinely novel signatures. -/

mutual
/-- Canonicalize a SymExpr: sort operands of commutative ops by hash. -/
partial def canonicalizeExpr {Reg : Type} [Hashable Reg] : SymExpr Reg → SymExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (canonicalizeExpr x)
  | .uext32 x => .uext32 (canonicalizeExpr x)
  | .sext8to32 x => .sext8to32 (canonicalizeExpr x)
  | .sext32to64 x => .sext32to64 (canonicalizeExpr x)
  | .add64 a b =>
    let a' := canonicalizeExpr a; let b' := canonicalizeExpr b
    if (hash a') < (hash b') then .add64 a' b' else .add64 b' a'
  | .xor64 a b =>
    let a' := canonicalizeExpr a; let b' := canonicalizeExpr b
    if (hash a') < (hash b') then .xor64 a' b' else .xor64 b' a'
  | .and64 a b =>
    let a' := canonicalizeExpr a; let b' := canonicalizeExpr b
    if (hash a') < (hash b') then .and64 a' b' else .and64 b' a'
  | .or64 a b =>
    let a' := canonicalizeExpr a; let b' := canonicalizeExpr b
    if (hash a') < (hash b') then .or64 a' b' else .or64 b' a'
  | .sub64 a b => .sub64 (canonicalizeExpr a) (canonicalizeExpr b)
  | .sub32 a b => .sub32 (canonicalizeExpr a) (canonicalizeExpr b)
  | .shl32 a b => .shl32 (canonicalizeExpr a) (canonicalizeExpr b)
  | .shl64 a b => .shl64 (canonicalizeExpr a) (canonicalizeExpr b)
  | .shr64 a b => .shr64 (canonicalizeExpr a) (canonicalizeExpr b)
  | .load w m addr => .load w (canonicalizeMem m) (canonicalizeExpr addr)
/-- Canonicalize a SymMem: normalize expressions within stores. -/
partial def canonicalizeMem {Reg : Type} [Hashable Reg] : SymMem Reg → SymMem Reg
  | .base => .base
  | .store w m addr val =>
    .store w (canonicalizeMem m) (canonicalizeExpr addr) (canonicalizeExpr val)
end

/-- Reassemble a list of PCs into a right-associated conjunction. -/
def reassembleAnd {Reg : Type} : List (SymPC Reg) → SymPC Reg
  | [] => .true
  | [x] => x
  | x :: xs => .and x (reassembleAnd xs)

/-- Canonicalize a SymPC:
    - eq: sort operands by hash (commutativity)
    - lt/le: canonicalize sub-expressions, keep direction
    - not(not(x)): eliminate double negation
    - and: flatten conjuncts, canonicalize each, sort by hash, right-associate -/
partial def canonicalizePC {Reg : Type} [Hashable Reg] : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq a b =>
    let a' := canonicalizeExpr a; let b' := canonicalizeExpr b
    if (hash a') < (hash b') then .eq a' b' else .eq b' a'
  | .lt a b => .lt (canonicalizeExpr a) (canonicalizeExpr b)
  | .le a b => .le (canonicalizeExpr a) (canonicalizeExpr b)
  | .not (.not x) => canonicalizePC x
  | .not x => .not (canonicalizePC x)
  | .and φ ψ =>
    let conjuncts := SymPC.conjuncts (.and φ ψ)
    let canon := conjuncts.map canonicalizePC
    let sorted := (canon.toArray.qsort (fun a b => (hash a) < (hash b))).toList
    reassembleAnd sorted

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

/-- Parse z3 check-sat results from stdout, skipping warnings, blank lines, and
    any other non-result output.  Only lines that are exactly "sat" or "unsat"
    count as results; they are collected in order, so result index i corresponds
    to the i-th check-sat query.  Any query whose result line is absent (e.g.
    because z3 errored) is simply not represented — callers treat missing entries
    conservatively (not-unsat). -/
def parseZ3Results (stdout : String) : Array Bool :=
  (stdout.splitOn "\n"
    |>.filter (fun l => l == "sat" || l == "unsat")
    |>.map (· == "unsat")).toArray

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

/-! ## Z3 Query Cache (Green-style)

Green (Visser et al. 2012) caches solver results by canonicalizing and hashing
the query formula.  On cache hit, the solver call is skipped entirely.

Pipeline: CANONIZE → HASH → CACHE LOOKUP → (miss?) Z3 → STORE

The cache maps: hash(canonicalizePC(assertion)) → Bool (true = UNSAT).
Implication queries (A → B) are represented as (A ∧ ¬B): UNSAT means A implies B.
Equivalence queries (A ↔ B) are decomposed into two implication queries. -/

/-- Z3 query cache: hash of canonicalized assertion formula → UNSAT result. -/
abbrev Z3Cache := Std.HashMap UInt64 Bool

/-- Cache key for an implication query "does A imply B?",
    i.e. is (A ∧ ¬B) UNSAT?  Canonicalizes the combined formula
    so semantically identical queries hash the same. -/
def z3ImplCacheKey {Reg : Type} [Hashable Reg] (a b : SymPC Reg) : UInt64 :=
  hash (canonicalizePC (.and a (.not b)))

/-- Run a batch of z3 implication queries with caching.
    Each query (A, B) checks: is (A ∧ ¬B) UNSAT? (i.e. does A → B?)
    Returns: (results array aligned with input, cache hits count).
    Updates the cache ref with new results. -/
def z3CheckImplCached {Reg : Type} [BEq Reg] [Hashable Reg] [ToString Reg]
    (cache : IO.Ref Z3Cache)
    (pairs : Array (SymPC Reg × SymPC Reg))
    (tmpFile : System.FilePath := ".lake/smt_cached.smt2") :
    IO (Array Bool × Nat) := do
  if pairs.size == 0 then return (#[], 0)
  let c ← cache.get
  -- Phase 1: check cache, collect misses.
  -- missOrigIdx[j] = index into `pairs`; missPairs[j] = the (A,B) pair.
  let mut results : Array (Option Bool) := Array.replicate pairs.size none
  let mut missOrigIdx : Array Nat := #[]
  let mut missPairs : Array (SymPC Reg × SymPC Reg) := #[]
  let mut hits : Nat := 0
  let mut pairIdx : Nat := 0
  for (a, b) in pairs do
    let key := z3ImplCacheKey a b
    match c.get? key with
    | some v => results := results.set! pairIdx (some v); hits := hits + 1
    | none =>
      missOrigIdx := missOrigIdx.push pairIdx
      missPairs := missPairs.push (a, b)
    pairIdx := pairIdx + 1
  -- Phase 2: batch z3 for cache misses
  if missPairs.size > 0 then
    let chunkSize := 1000
    let mut allMissResults : Array Bool := #[]
    let mut chunkStart := 0
    while chunkStart < missPairs.size do
      let chunkEnd := min (chunkStart + chunkSize) missPairs.size
      let chunk := missPairs.extract chunkStart chunkEnd
      let mut regNames : Std.HashSet String := {}
      let mut needsMem := false
      for (a, b) in chunk do
        regNames := SymPC.collectRegNames a regNames
        regNames := SymPC.collectRegNames b regNames
        if SymPC.hasLoad a || SymPC.hasLoad b then needsMem := true
      let mut script := smtPreamble regNames needsMem
      for (a, b) in chunk do
        script := script ++ "(push)\n"
        script := script ++ s!"(assert (and {SymPC.toSMTLib a} (not {SymPC.toSMTLib b})))\n"
        script := script ++ "(check-sat)\n"
        script := script ++ "(pop)\n"
      script := script ++ "(exit)\n"
      IO.FS.writeFile tmpFile script
      let z3Out ← IO.Process.output { cmd := "z3", args := #[tmpFile.toString] }
      allMissResults := allMissResults ++ parseZ3Results z3Out.stdout
      chunkStart := chunkEnd
    -- Store results in cache and in output array
    let mut c' ← cache.get
    let mut missIdx : Nat := 0
    for (a, b) in missPairs do
      let isUnsat := if h : missIdx < allMissResults.size then allMissResults[missIdx] else false
      if h2 : missIdx < missOrigIdx.size then
        results := results.set! missOrigIdx[missIdx] (some isUnsat)
      c' := c'.insert (z3ImplCacheKey a b) isUnsat
      missIdx := missIdx + 1
    cache.set c'
  -- Phase 3: unwrap
  return (results.map (fun r => r.getD false), hits)

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
def computePCSignature {Reg : Type} [DecidableEq Reg] [Hashable Reg] [Hashable (SymPC Reg)]
    (closure : Array (SymPC Reg)) (pc : SymPC Reg) : List Bool :=
  -- Canonicalize then extract conjuncts for O(1) membership checks.
  -- Canonicalization ensures that e.g. eq(a,b) and eq(b,a) hash identically,
  -- catching more syntactic matches before falling through to z3.
  let pcConjList := SymPC.conjuncts (canonicalizePC pc)
  let pcConjSet : Std.HashSet (SymPC Reg) :=
    pcConjList.foldl (fun s c => s.insert c) {}
  closure.toList.map fun guardPC =>
    match guardPC with
    | .true => true  -- everything implies .true
    | _ => pcConjSet.contains (canonicalizePC guardPC)

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

/-- Check if a SymExpr transitively references a specific register.
    Does NOT recurse into SymMem (only checks expression structure). -/
partial def exprReferencesReg {Reg : Type} [BEq Reg] (r : Reg) : SymExpr Reg → Bool
  | .reg r' => r == r'
  | .const _ => false
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e => exprReferencesReg r e
  | .add64 a b | .sub64 a b | .xor64 a b | .and64 a b | .or64 a b
  | .shl64 a b | .shr64 a b | .sub32 a b | .shl32 a b =>
    exprReferencesReg r a || exprReferencesReg r b
  | .load _ _ addr => exprReferencesReg r addr

/-- Classification of a block's rip target expression. -/
inductive RipTargetClass where
  | direct (addr : UInt64)              -- constant target (jump, call, or tail call)
  | ret                                  -- load from stack area (return instruction)
  | computed (expr : SymExpr Amd64Reg)  -- register value or complex expression
  deriving Inhabited

/-- Classify the rip target of a branch's substitution.
    - direct: rip = const addr (jump, call, or tail call)
    - ret: rip = load(_, mem, addr) where addr references any stack register
      (rsp for non-frame-pointer code, rbp for frame-pointer code)
    - computed: rip = register or complex expression (switch tables, etc.) -/
def classifyRipTarget (ip_reg : Amd64Reg) (stackRegs : Array Amd64Reg) (sub : SymSub Amd64Reg) : RipTargetClass :=
  match sub.regs ip_reg with
  | .const addr => .direct addr
  | .load _ _ addr =>
    if stackRegs.any (fun r => exprReferencesReg r addr) then .ret
    else .computed (sub.regs ip_reg)
  | expr => .computed expr

/-- Extract a return address from a branch's memory store chain.
    Walks the store chain (outermost → innermost) looking for a constant value
    stored to a stack-relative address. For x86-64, a `call` pushes the return
    address: store(W64, mem, rsp-8, const return_addr). The return address is the
    continuation block after the call.
    Returns the first matching constant found. -/
partial def extractCallReturnAddr {Reg : Type} [BEq Reg]
    (stackReg : Reg) : SymMem Reg → Option UInt64
  | .base => none
  | .store _w innerMem storeAddr storeVal =>
    match storeVal with
    | .const retAddr =>
      if exprReferencesReg stackReg storeAddr then some retAddr
      else extractCallReturnAddr stackReg innerMem
    | _ => extractCallReturnAddr stackReg innerMem

/-- Detect whether a branch is a call site (not a tail call or plain jump).
    A call: rip = const target AND stores a constant return address to the stack.
    A tail call or plain jump: rip = const target but NO return address pushed.
    Returns (callee_entry, continuation_address) for calls. -/
def detectCallSite {Reg : Type} [BEq Reg]
    (ip_reg stackReg : Reg) (sub : SymSub Reg) : Option (UInt64 × UInt64) :=
  match sub.regs ip_reg with
  | .const target =>
    match extractCallReturnAddr stackReg sub.mem with
    | some retAddr => some (target, retAddr)
    | none => none
  | _ => none

/-- Pretty-print a rip expression for diagnostic logging. -/
partial def ppRipExpr : SymExpr Amd64Reg → String
  | .const v => s!"0x{String.mk (Nat.toDigits 16 v.toNat)}"
  | .reg r => toString r
  | .load _ _ addr => s!"load(mem, {ppRipExpr addr})"
  | .add64 a b => s!"({ppRipExpr a}+{ppRipExpr b})"
  | .sub64 a b => s!"({ppRipExpr a}-{ppRipExpr b})"
  | _ => "..."

/-- Build CFG successor map from body branches: source rip → target rips.
    For constant rip targets: adds a direct edge src → tgt.
    For indirect jumps (non-constant rip): adds edges to all blocks in the
    same function (intra-function fan-out). This ensures switch/case blocks
    are reachable from the function entry. Cross-function indirect jumps
    don't add edges to ALL blocks (which would merge everything into one SCC). -/
def buildCFGSuccessors {Reg : Type} [BEq Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (funcBlockAddrs : Std.HashMap UInt64 (Array UInt64) := {}) :
    Std.HashMap UInt64 (Array UInt64) := Id.run do
  let mut succs : Std.HashMap UInt64 (Array UInt64) := {}
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc with
    | some src =>
      match extractRipTarget ip_reg b.sub with
      | some tgt =>
        let existing := succs.getD src #[]
        unless existing.contains tgt do
          succs := succs.insert src (existing.push tgt)
      | none =>
        -- Indirect jump: add edges to all blocks in same function
        match funcBlockAddrs.get? src with
        | some siblings =>
          let mut existing := succs.getD src #[]
          for tgt in siblings do
            unless existing.contains tgt || tgt == src do
              existing := existing.push tgt
          succs := succs.insert src existing
        | none => pure ()  -- no function info, treat as exit
    | none => pure ()
  return succs

/-- Format a UInt64 as a hex address string. -/
private def fmtAddr (a : UInt64) : String :=
  s!"0x{String.mk (Nat.toDigits 16 a.toNat)}"

/-- Compute return edges for the interprocedural CFG.
    For each return block (rip = load from stack), adds edges to the
    continuation blocks of all callers of the return block's function.

    Algorithm:
    1. Scan all branches to find call sites: callee_entry → [continuation_addr]
    2. Scan all branches to find return blocks: block addr where rip = load(mem, rsp)
    3. For each return block in function F, add edges to all callers' continuations

    This completes the CFG for standard x86-64 call/ret patterns.
    Tail calls (rip = const, no stack push) produce no return edges — correct,
    since the callee returns to the caller's caller, not to us. -/
def buildReturnEdges
    (ip_reg : Amd64Reg)
    (stackRegs : Array Amd64Reg)   -- registers that access the stack area (rsp, rbp)
    (callStackReg : Amd64Reg)      -- register used by CALL instruction to push return addr (rsp)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (blockToFunc : Std.HashMap UInt64 UInt64)
    (log : String → IO Unit) :
    IO (Std.HashMap UInt64 (Array UInt64)) := do
  -- Phase 1: Classify all branches and collect call sites
  let mut callSites : Std.HashMap UInt64 (Array UInt64) := {}  -- callee_entry → [continuation_addrs]
  let mut callCount : Nat := 0
  let mut tailCallCount : Nat := 0
  let mut returnBlockAddrs : Std.HashSet UInt64 := {}
  let mut computedJumpCount : Nat := 0
  let mut directJumpCount : Nat := 0
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc with
    | some src =>
      match classifyRipTarget ip_reg stackRegs b.sub with
      | .direct _target =>
        match detectCallSite ip_reg callStackReg b.sub with
        | some (callee, continuation) =>
          callCount := callCount + 1
          let existing := callSites.getD callee #[]
          unless existing.contains continuation do
            callSites := callSites.insert callee (existing.push continuation)
          log s!"    call: {fmtAddr src} → {fmtAddr callee} (ret to {fmtAddr continuation})"
        | none =>
          -- No return address pushed: either intra-function jump or tail call
          let srcFunc := blockToFunc.getD src 0
          let tgtFunc := blockToFunc.getD _target 0
          if srcFunc != 0 && tgtFunc != 0 && srcFunc != tgtFunc then
            tailCallCount := tailCallCount + 1
            log s!"    tail-call: {fmtAddr src} → {fmtAddr _target}"
          else
            directJumpCount := directJumpCount + 1
      | .ret =>
        unless returnBlockAddrs.contains src do
          returnBlockAddrs := returnBlockAddrs.insert src
          log s!"    return: {fmtAddr src} (rip={ppRipExpr (b.sub.regs ip_reg)})"
      | .computed expr =>
        computedJumpCount := computedJumpCount + 1
        -- Only log unique computed jump sources
        log s!"    computed: {fmtAddr src} (rip={ppRipExpr expr})"
    | none => pure ()
  -- Phase 2: Build return edges
  -- For functions WITH return blocks: return_block → caller's continuation
  -- For functions WITHOUT return blocks (external/opaque): call_site → continuation
  let mut returnEdges : Std.HashMap UInt64 (Array UInt64) := {}
  let mut retEdgeCount : Nat := 0
  let mut callContEdgeCount : Nat := 0
  -- 2a: Functions with detected return blocks get return edges
  for retAddr in returnBlockAddrs do
    let funcEntry := blockToFunc.getD retAddr 0
    if funcEntry != 0 then
      match callSites.get? funcEntry with
      | some continuations =>
        let mut existing := returnEdges.getD retAddr #[]
        for cont in continuations do
          unless existing.contains cont do
            existing := existing.push cont
            retEdgeCount := retEdgeCount + 1
            log s!"    ret-edge: {fmtAddr retAddr} → {fmtAddr cont} (return from {fmtAddr funcEntry})"
        returnEdges := returnEdges.insert retAddr existing
      | none => pure ()
  -- 2b: Collect which functions have return blocks
  let mut funcsWithReturn : Std.HashSet UInt64 := {}
  for retAddr in returnBlockAddrs do
    let funcEntry := blockToFunc.getD retAddr 0
    if funcEntry != 0 then
      funcsWithReturn := funcsWithReturn.insert funcEntry
  -- 2c: For calls to functions WITHOUT return blocks (external/opaque functions),
  -- add call-continuation edges: src → continuation.
  -- This models the call/return as a pass-through from the caller's perspective.
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc with
    | some src =>
      match detectCallSite ip_reg callStackReg b.sub with
      | some (callee, continuation) =>
        -- Only add call-continuation edge if callee has no return blocks
        unless funcsWithReturn.contains callee do
          let existing := returnEdges.getD src #[]
          unless existing.contains continuation do
            returnEdges := returnEdges.insert src (existing.push continuation)
            callContEdgeCount := callContEdgeCount + 1
            log s!"    call-cont: {fmtAddr src} → {fmtAddr continuation} (opaque call to {fmtAddr callee})"
      | none => pure ()
    | none => pure ()
  log s!"  Classification: {callCount} calls, {tailCallCount} tail-calls, {returnBlockAddrs.size} return blocks, {computedJumpCount} computed jumps, {directJumpCount} intra-function jumps"
  log s!"  Return edges: {retEdgeCount} ret-edges + {callContEdgeCount} call-continuation edges = {retEdgeCount + callContEdgeCount} total"
  return returnEdges

/-! ## Bourdoncle WTO (Weak Topological Order)

Bourdoncle 1993 "Efficient chaotic iteration strategies with widenings" —
produces a hierarchical decomposition of SCCs with identified loop headers.
`vertex v` = DAG node (no back edge targets it).
`component head children` = SCC with `head` as the loop header and
`children` processed in WTO order. Nested components get their own inner
fixpoint before the outer loop widens. -/

inductive WTOComponent where
  | vertex : UInt64 → WTOComponent
  | component : UInt64 → Array WTOComponent → WTOComponent
  deriving Inhabited

/-- Collect all block addresses mentioned in a WTO component. -/
partial def WTOComponent.addrs : WTOComponent → Array UInt64
  | .vertex v => #[v]
  | .component h cs => cs.foldl (fun acc c => acc ++ c.addrs) #[h]

/-- Shared state for Bourdoncle WTO algorithm. -/
structure WTOState where
  dfn   : Std.HashMap UInt64 Nat
  num   : Nat
  stack : Array UInt64

/-- Recursive visit in Bourdoncle's WTO algorithm (1993).
    Returns the minimum dfn reachable from v (the "head" value).
    Pushes WTO elements into `elemsRef` (the current nesting level).
    Elements are appended in DFS postorder; caller reverses for WTO order. -/
partial def wtoVisit
    (succs : Std.HashMap UInt64 (Array UInt64))
    (stRef : IO.Ref WTOState)
    (elemsRef : IO.Ref (Array WTOComponent))
    (v : UInt64) : IO Nat := do
  let st ← stRef.get
  let vDfn := st.num + 1
  stRef.set { dfn := st.dfn.insert v vDfn, num := vDfn, stack := st.stack.push v }
  let mut head := vDfn
  let mut isLoop := false
  let successors := succs.getD v #[]
  for w in successors do
    let wDfn := (← stRef.get).dfn.getD w 0
    let minVal ← if wDfn == 0 then wtoVisit succs stRef elemsRef w
                  else pure wDfn
    if minVal <= head then
      head := minVal
      isLoop := true
  if head == vDfn then
    let maxVal := 1000000000
    stRef.modify fun s => { s with dfn := s.dfn.insert v maxVal }
    if isLoop then
      let mut st' ← stRef.get
      while st'.stack.size > 0 && st'.stack[st'.stack.size - 1]! != v do
        let w := st'.stack[st'.stack.size - 1]!
        st' := { st' with stack := st'.stack.pop, dfn := st'.dfn.insert w 0 }
      st' := { st' with stack := st'.stack.pop }
      stRef.set st'
      let childRef ← IO.mkRef (#[] : Array WTOComponent)
      for w in successors do
        let wDfn := (← stRef.get).dfn.getD w 0
        if wDfn == 0 then
          let _ ← wtoVisit succs stRef childRef w
      let children ← childRef.get
      elemsRef.modify (·.push (.component v children))
    else
      stRef.modify fun s => { s with stack := s.stack.pop }
      elemsRef.modify (·.push (.vertex v))
  return head

/-- Compute the Bourdoncle WTO decomposition of a CFG.
    `entries` are the DFS roots; `succs` maps each node to its successors.
    Returns WTO elements in topological order (DAG predecessors first).
    SCC components are nested: inner loops converge before outer ones. -/
def computeWTO
    (entries : Array UInt64)
    (succs : Std.HashMap UInt64 (Array UInt64)) :
    IO (Array WTOComponent) := do
  let stRef ← IO.mkRef ({ dfn := {}, num := 0, stack := #[] } : WTOState)
  let elemsRef ← IO.mkRef (#[] : Array WTOComponent)
  for entry in entries do
    let entryDfn := (← stRef.get).dfn.getD entry 0
    if entryDfn == 0 then
      let _ ← wtoVisit succs stRef elemsRef entry
  elemsRef.get

/-- Pretty-print a WTO decomposition for logging. -/
partial def ppWTO (components : Array WTOComponent) : String :=
  let parts := components.map fun c => match c with
    | .vertex v => s!"0x{String.mk (Nat.toDigits 16 v.toNat)}"
    | .component h cs =>
      s!"(0x{String.mk (Nat.toDigits 16 h.toNat)} {ppWTO cs})"
  " ".intercalate parts.toList

/-- Count unique addresses in a WTO decomposition. -/
partial def wtoUniqueAddrs (components : Array WTOComponent) : Std.HashSet UInt64 :=
  components.foldl (fun acc c => match c with
    | .vertex v => acc.insert v
    | .component h cs =>
      let inner := wtoUniqueAddrs cs
      inner.fold (fun s a => s.insert a) (acc.insert h))
    {}

/-- Count top-level vertices and components in a WTO (non-recursive). -/
def wtoTopLevelStats (components : Array WTOComponent) : Nat × Nat :=
  components.foldl (fun (dags, sccs) c => match c with
    | .vertex _ => (dags + 1, sccs)
    | .component _ _ => (dags, sccs + 1))
    (0, 0)

/-- Count vertices and components in a WTO (recursive — DAG vertices at all nesting levels). -/
partial def wtoStats (components : Array WTOComponent) : Nat × Nat :=
  components.foldl (fun (dags, sccs) c => match c with
    | .vertex _ => (dags + 1, sccs)
    | .component _ cs =>
      let (innerDags, innerSccs) := wtoStats cs
      (dags + innerDags, sccs + 1 + innerSccs))
    (0, 0)

/-- Detailed WTO structure logging: print each SCC with head, members, and nesting. -/
partial def ppWTODetailed (log : String → IO Unit) (components : Array WTOComponent) (indent : String := "") : IO Unit := do
  for c in components do
    match c with
    | .vertex v =>
      log s!"{indent}vertex 0x{String.mk (Nat.toDigits 16 v.toNat)}"
    | .component h cs =>
      let allAddrs := cs.foldl (fun acc child => acc ++ child.addrs) (#[h] : Array UInt64)
      log s!"{indent}SCC head=0x{String.mk (Nat.toDigits 16 h.toNat)} members={allAddrs.size} [{", ".intercalate (allAddrs.toList.map (fun a => s!"0x{String.mk (Nat.toDigits 16 a.toNat)}"))}]"
      log s!"{indent}  children ({cs.size}):"
      ppWTODetailed log cs (indent ++ "    ")

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

/-- A function specification for dispatch loop analysis. -/
structure FunctionSpec where
  name : String
  entryAddr : UInt64
  blocks : List String  -- raw IRSB strings
  deriving Inhabited

/-- Per-function stabilization with optional initial frontier seeding.
    When initialFrontier is non-empty, those branches are added to the
    initial state (along with skip) instead of starting from skip alone.
    This is used to seed call-expanded results into the frontier without
    putting them in the body (which would cause expression nesting). -/
def computeFunctionStabilization {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg] [ToString Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (maxIter : Nat) (log : String → IO Unit)
    (z3cache : IO.Ref Z3Cache)
    (initialFrontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[])
    (closureBody : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]) :
    IO (Option (Nat × Array (Branch (SymSub Reg) (SymPC Reg)))) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  -- Use closureBody for closure extraction if provided, otherwise use bodyArr
  let closureSrc := if closureBody.size > 0 then closureBody else bodyArr
  let (closure, ripCount, dataCount) := extractClosure ip_reg closureSrc (dataOnly := true)
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  current := current.insert initBranch
  -- initialFrontier seeded into current AFTER closedness check (needs projection)
  -- Compute closed projection: transitive register dependency closure
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
  -- Convergence via PC signature: syntactic fast-path + z3 semantic check.
  -- convRep{PCs,SynSigs,SemSigs}: one entry per discovered equivalence class.
  -- SynSig = which closure PCs the branch syntactically implies (List Bool).
  -- SemSig = which closure PCs the branch semantically implies (Array Bool);
  --          computed lazily via z3 the first time a syntactic mismatch occurs.
  let mut convRepPCs     : Array (SymPC Reg)          := #[initBranch.pc]
  let mut convRepSynSigs : Array (List Bool)           := #[computePCSignature closure initBranch.pc]
  let mut convRepSemSigs : Array (Option (Array Bool)) := #[none]
  -- Build initial frontier: skip + structurally-unique simplified seeds.
  let mut frontierSet : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {initBranch}
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[initBranch]
  for b in initialFrontier do
    match simplifyBranchFull b with
    | none => pure ()
    | some sb =>
      let zb := zeroNonProjected closedRegs ip_reg sb
      unless frontierSet.contains zb do
        frontierSet := frontierSet.insert zb
        convRepPCs     := convRepPCs.push zb.pc
        convRepSynSigs := convRepSynSigs.push (computePCSignature closure zb.pc)
        convRepSemSigs := convRepSemSigs.push none
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
    -- Phase 1: structural dedup — collect all branches not already in current
    let mut semCands : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for b in simplified do
      if current.contains b then
        dupes := dupes + 1
      else
        current := current.insert b  -- ALL structurally distinct branches kept for summary
        semCands := semCands.push b
    -- Phase 2: PC-signature convergence (syntactic fast-path + z3 semantic).
    -- For each candidate, compute its signature: which closure PCs does it imply?
    -- Fast path: syntactic sig matches an existing rep sig → collapse.
    -- Slow path (z3): for candidates with new syntactic sigs, compute semantic sig
    --   (for each closure PC phi_i, is branch.pc AND NOT phi_i UNSAT?) and
    --   compare against rep semantic sigs.
    let mut semCollapsed : Nat := 0
    if semCands.size > 0 then
      -- Compute syntactic sigs for all candidates
      let candSynSigs := semCands.map (fun c => computePCSignature closure c.pc)
      -- Fast path: which candidates have a syntactic sig matching an existing rep?
      let mut synMatched : Std.HashSet Nat := {}
      for ci in [:semCands.size] do
        let csig := candSynSigs[ci]!
        let mut ri := 0
        while ri < convRepSynSigs.size do
          if convRepSynSigs[ri]! == csig then
            synMatched := synMatched.insert ci
            ri := convRepSynSigs.size  -- break
          ri := ri + 1
      -- Collect z3 candidates: those with no syntactic match
      let mut z3CandIdxs : Array Nat := #[]
      for ci in [:semCands.size] do
        unless synMatched.contains ci do
          z3CandIdxs := z3CandIdxs.push ci
      -- Semantic path: only if there are unmatched candidates and closure is non-empty
      let mut candSemSigsArr : Array (Option (Array Bool)) := Array.replicate semCands.size none
      let mut totalZ3Queries := 0
      let mut totalZ3CacheHits := 0
      let mut semMatched : Std.HashSet Nat := {}
      if z3CandIdxs.size > 0 && closure.size > 0 then
        let n := closure.size
        -- Build batch of PCs needing semantic sig computation:
        -- (1) reps with uncomputed sem sigs, (2) z3 candidate branch PCs.
        -- Use Array.extract to avoid [i]! on SymPC/Branch arrays.
        let mut batchPCs      : Array (SymPC Reg) := #[]
        let mut batchIsRep    : Array Bool        := #[]
        let mut batchRepIdxs  : Array Nat         := #[]
        let mut batchCandIdxs : Array Nat         := #[]
        for ri in [:convRepPCs.size] do
          match convRepSemSigs[ri]? with
          | some none =>
            for pc in convRepPCs.extract ri (ri + 1) do
              batchPCs := batchPCs.push pc
            batchIsRep    := batchIsRep.push true
            batchRepIdxs  := batchRepIdxs.push ri
            batchCandIdxs := batchCandIdxs.push 0  -- dummy
          | _ => pure ()
        for ci in z3CandIdxs do
          for b in semCands.extract ci (ci + 1) do
            batchPCs := batchPCs.push b.pc
          batchIsRep    := batchIsRep.push false
          batchRepIdxs  := batchRepIdxs.push 0  -- dummy
          batchCandIdxs := batchCandIdxs.push ci
        -- Batch z3 with caching: for each pc in batchPCs, n queries (one per closure PC).
        let mut convPairs : Array (SymPC Reg × SymPC Reg) := #[]
        for pc in batchPCs do
          for phi in closure do
            convPairs := convPairs.push (pc, phi)
        let (allSemResults, convHits) ← z3CheckImplCached z3cache convPairs ".lake/smt_semsig.smt2"
        totalZ3Queries := convPairs.size
        totalZ3CacheHits := convHits
        -- Assign sem sigs: allSemResults[si*n .. (si+1)*n] for batchPCs[si]
        let mut updatedRepSemSigs := convRepSemSigs
        let mut si := 0
        for isRep in batchIsRep do
          let semSig := allSemResults.extract (si * n) ((si + 1) * n)
          if isRep then
            let ri := batchRepIdxs[si]!
            updatedRepSemSigs := updatedRepSemSigs.set! ri (some semSig)
          else
            let ci := batchCandIdxs[si]!
            candSemSigsArr := candSemSigsArr.set! ci (some semSig)
          si := si + 1
        convRepSemSigs := updatedRepSemSigs
        -- Compare each z3 cand's semantic sig against all rep semantic sigs
        for ci in z3CandIdxs do
          if let some candSem := candSemSigsArr[ci]! then
            let mut ri := 0
            let mut matched := false
            while !matched && ri < convRepSemSigs.size do
              if let some repSem := convRepSemSigs[ri]! then
                if candSem == repSem then
                  semMatched := semMatched.insert ci
                  matched := true
              ri := ri + 1
      log s!"    z3 conv: {totalZ3Queries}q (hits={totalZ3CacheHits} misses={totalZ3Queries - totalZ3CacheHits}) → syn-collapsed={synMatched.size} sem-collapsed={semMatched.size}"
      -- Classify: collapse or promote to new equivalence class
      for ci in [:semCands.size] do
        if synMatched.contains ci || semMatched.contains ci then
          semCollapsed := semCollapsed + 1
        else
          for b in semCands.extract ci (ci + 1) do
            convRepPCs     := convRepPCs.push b.pc
            convRepSynSigs := convRepSynSigs.push candSynSigs[ci]!
            convRepSemSigs := convRepSemSigs.push candSemSigsArr[ci]!
            newBranches    := newBranches.push b
    let t_end ← IO.monoMsNow
    log s!"    K={k}: |S|={current.size} |new|={newBranches.size} |conv_reps|={convRepSynSigs.size} pairs={pairsComposed} skipped={skipped} dropped={dropped}+{droppedSimplify} dupes={dupes} sem_collapsed={semCollapsed} {t_end - t_start}ms"
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
        -- Run z3 semantic equivalence check via cached implication pairs.
        -- Equivalence (A ↔ B) = (A→B) ∧ (B→A): decompose into two implication queries.
        let mut closednessViolations : Nat := 0
        if closedQueryPairs.size > 0 then
          -- Build forward (cp→rp) and reverse (rp→cp) implication pairs
          let mut fwdPairs : Array (SymPC Reg × SymPC Reg) := #[]
          let mut revPairs : Array (SymPC Reg × SymPC Reg) := #[]
          for (cp, rp) in closedQueryPairs do
            fwdPairs := fwdPairs.push (cp, rp)
            revPairs := revPairs.push (rp, cp)
          let (fwdResults, fwdHits) ← z3CheckImplCached z3cache fwdPairs ".lake/smt_closedness.smt2"
          let (revResults, revHits) ← z3CheckImplCached z3cache revPairs ".lake/smt_closedness.smt2"
          -- A pair is equivalent iff both forward AND reverse implications hold
          let mut closedByZ3 : Std.HashSet Nat := {}
          for i in [:closedQueryPairs.size] do
            if h1 : i < fwdResults.size then
              if h2 : i < revResults.size then
                if fwdResults[i] && revResults[i] then
                  closedByZ3 := closedByZ3.insert closedQueryLiftedIdx[i]!
          -- Violations: lifted PCs not closed by z3
          for gIdx in liftedNeedingCheck do
            unless closedByZ3.contains gIdx do
              closednessViolations := closednessViolations + 1
          let clTotalQueries := closedQueryPairs.size * 2
          log s!"    [closedness] z3: {clTotalQueries} queries (hits={fwdHits + revHits} misses={clTotalQueries - fwdHits - revHits}), {closedByZ3.size} closed, {closednessViolations} violations"
        let isClosed := closednessViolations == 0
        log s!"    [closedness] closure closed: {if isClosed then "YES" else "NO"}, violations={closednessViolations}"
      return some (k, summaryArr)
    frontier := newBranches
  return none

/-! ## Unified WTO Fixpoint

One unified WTO over all blocks. DAG blocks are processed once (single
composition pass). SCC blocks are iterated until convergence. The WTO
nesting structure ensures inner loops converge before outer ones. -/

/-- Process a DAG block: compose its body branches with cached successors.
    Branches whose rip target is not in cache are kept as exit branches. -/
def processDAGBlock
    (ip_reg : Amd64Reg)
    (addr : UInt64)
    (blocksByAddr : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (cache : IO.Ref (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))))
    (returnEdges : Std.HashMap UInt64 (Array UInt64))
    (log : String → IO Unit) : IO Unit := do
  let isa := vexSummaryISA Amd64Reg
  let bodyBranches := blocksByAddr.getD addr #[]
  let cacheContents ← cache.get
  let mut result : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  let mut composed : Nat := 0
  let mut dropped : Nat := 0
  let mut retComposed : Nat := 0
  let mut retDropped : Nat := 0
  for b in bodyBranches do
    match extractRipTarget ip_reg b.sub with
    | some target =>
      match cacheContents.get? target with
      | some cachedBranches =>
        for cb in cachedBranches do
          composed := composed + 1
          let comp := b.compose isa cb
          match simplifyBranch comp with
          | none => dropped := dropped + 1
          | some b' => result := result.push b'
      | none => result := result.push b  -- exit branch, keep as-is
    | none =>
      -- Non-constant rip (return or computed jump).
      -- Consult return edges: compose with each return-edge target's cached branches.
      -- The composition produces PC with load(mem, rbp+0x8) == cont_addr;
      -- simplifyBranchFull resolves the load-after-store, collapsing to true or dropping.
      match returnEdges.get? addr with
      | some retTargets =>
        for tgt in retTargets do
          match cacheContents.get? tgt with
          | some cachedBranches =>
            for cb in cachedBranches do
              retComposed := retComposed + 1
              let comp := b.compose isa cb
              match simplifyBranchFull comp with
              | none => retDropped := retDropped + 1
              | some b' => result := result.push b'
          | none => pure ()  -- target not cached yet, skip
        -- If no return-edge compositions survived, keep original as exit
        if retTargets.isEmpty then result := result.push b
      | none => result := result.push b  -- no return edges, keep as exit
  -- Only cache non-empty results. Blocks with 0 body (like _exit) stay uncached
  -- so predecessors keep their original branches (exit branches).
  if result.size > 0 then
    cache.modify (·.insert addr result)
  log s!"    DAG 0x{String.mk (Nat.toDigits 16 addr.toNat)}: {bodyBranches.size} body → {result.size} cached ({composed} composed, {dropped} dropped, {retComposed} ret-composed, {retDropped} ret-dropped)"

/-- Process an SCC component via convergence fixpoint.
    Collects body branches for all SCC member blocks, splits into internal
    (target ∈ SCC) vs external (pre-composed with cache), then runs the
    standard convergence loop on the internal body with external seeds as
    initial frontier. On convergence, groups result by rip-guard address
    and updates cache per-block. -/
def processSCCStabilization
    (ip_reg : Amd64Reg)
    (sccAddrs : Array UInt64)
    (blocksByAddr : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (cache : IO.Ref (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))))
    (returnEdges : Std.HashMap UInt64 (Array UInt64))
    (log : String → IO Unit)
    (z3cache : IO.Ref Z3Cache)
    (blockToFunc : Std.HashMap UInt64 UInt64 := {}) : IO Unit := do
  let isa := vexSummaryISA Amd64Reg
  let sccSet : Std.HashSet UInt64 := sccAddrs.foldl (fun s a => s.insert a) {}
  -- Collect all body branches for SCC member blocks
  let mut allBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  for addr in sccAddrs do
    for b in blocksByAddr.getD addr #[] do
      allBody := allBody.push b
  -- Split into internal body (target ∈ SCC) vs external seeds (pre-composed with cache)
  let cacheContents ← cache.get
  let mut internalBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  let mut externalSeeds : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  let mut exitBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  let mut callsExpanded : Nat := 0
  let mut droppedExp : Nat := 0
  let mut retExpanded : Nat := 0
  let mut retDropped : Nat := 0
  for b in allBody do
    match extractRipGuard ip_reg b.pc with
    | none => exitBranches := exitBranches.push b
    | some srcAddr =>
    match extractRipTarget ip_reg b.sub with
    | some target =>
      if sccSet.contains target then
        -- Check if this SCC-internal target already has cached results
        -- (from inner WTO component processing)
        match cacheContents.get? target with
        | some cachedBranches =>
          -- Pre-converged inner block: compose with cached result → seeds
          callsExpanded := callsExpanded + 1
          for cb in cachedBranches do
            let composed := b.compose isa cb
            match simplifyBranch composed with
            | none => droppedExp := droppedExp + 1
            | some b' => externalSeeds := externalSeeds.push b'
        | none =>
          -- Not yet cached: stays in convergence body
          internalBody := internalBody.push b
      else
        match cacheContents.get? target with
        | some cachedBranches =>
          callsExpanded := callsExpanded + 1
          for cb in cachedBranches do
            let composed := b.compose isa cb
            match simplifyBranch composed with
            | none => droppedExp := droppedExp + 1
            | some b' => externalSeeds := externalSeeds.push b'
        | none => exitBranches := exitBranches.push b  -- exit
    | none =>
      -- Non-constant rip: consult return edges for this source block.
      -- Return-edge targets in the SCC → internal body (after composition).
      -- Return-edge targets outside the SCC → external seeds (after composition).
      match returnEdges.get? srcAddr with
      | some retTargets =>
        for tgt in retTargets do
          if sccSet.contains tgt then
            match cacheContents.get? tgt with
            | some cachedBranches =>
              -- Return target is in SCC and cached (pre-converged inner block)
              -- → compose and add to external seeds
              for cb in cachedBranches do
                retExpanded := retExpanded + 1
                let comp := b.compose isa cb
                match simplifyBranchFull comp with
                | none => retDropped := retDropped + 1
                | some b' => externalSeeds := externalSeeds.push b'
            | none =>
              -- Target is in SCC but not cached yet — compose with raw body → internal
              for cb in blocksByAddr.getD tgt #[] do
                retExpanded := retExpanded + 1
                let comp := b.compose isa cb
                match simplifyBranchFull comp with
                | none => retDropped := retDropped + 1
                | some b' => internalBody := internalBody.push b'
          else
            -- Return goes outside the SCC — compose and add to external seeds
            match cacheContents.get? tgt with
            | some cachedBranches =>
              for cb in cachedBranches do
                retExpanded := retExpanded + 1
                let comp := b.compose isa cb
                match simplifyBranchFull comp with
                | none => retDropped := retDropped + 1
                | some b' => externalSeeds := externalSeeds.push b'
            | none => pure ()  -- target not cached, skip
        if retTargets.isEmpty then exitBranches := exitBranches.push b
      | none => exitBranches := exitBranches.push b  -- no return edges
  log s!"    SCC [{sccAddrs.size} blocks]: {allBody.size} body → {internalBody.size} internal + {externalSeeds.size} ext-seeds + {exitBranches.size} exit ({callsExpanded} call-exp, {droppedExp} call-dropped, {retExpanded} ret-exp, {retDropped} ret-dropped)"
  -- Use existing convergence loop with internal body and external seeds as frontier
  let initialFrontier := externalSeeds ++ exitBranches
  -- Compute function-scope closure body: include ALL blocks from every function
  -- that has blocks in this SCC. This ensures closure PCs match function-level scope.
  let mut closureBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  if blockToFunc.size > 0 then
    let mut funcEntries : Std.HashSet UInt64 := {}
    for addr in sccAddrs do
      match blockToFunc.get? addr with
      | some funcEntry => funcEntries := funcEntries.insert funcEntry
      | none => pure ()
    -- Collect all blocks belonging to those functions
    for (addr, branches) in blocksByAddr do
      match blockToFunc.get? addr with
      | some funcEntry =>
        if funcEntries.contains funcEntry then
          for b in branches do
            closureBody := closureBody.push b
      | none => pure ()
  match ← computeFunctionStabilization ip_reg internalBody 200 log z3cache
           (initialFrontier := initialFrontier)
           (closureBody := closureBody) with
  | some (k, summaryArr) =>
    -- Group converged branches by rip-guard address → update cache per-block
    let mut perBlock : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
    for b in summaryArr do
      match extractRipGuard ip_reg b.pc with
      | some addr =>
        let arr := perBlock.getD addr #[]
        perBlock := perBlock.insert addr (arr.push b)
      | none => pure ()  -- skip branches without rip guard (e.g., skip branch)
    for addr in sccAddrs do
      let blockSummary := perBlock.getD addr #[]
      cache.modify (·.insert addr blockSummary)
    log s!"    SCC converged at K={k}, {summaryArr.size} total branches"
    for addr in sccAddrs do
      let n := perBlock.getD addr #[] |>.size
      log s!"      0x{String.mk (Nat.toDigits 16 addr.toNat)}: {n} branches"
  | none =>
    log s!"    SCC DID NOT CONVERGE"

mutual

/-- Process a multi-function SCC: FLAT outer loop over function summaries.
    All blocks in the multi-func SCC are handled in one flat loop — no recursive
    WTO processing of sub-components (which causes exponential re-analysis with
    deeply nested WTO structures). Each outer round runs
    computeFunctionStabilization per function with cache-aware splitting.
    Converges when all function summaries stabilize. -/
partial def processMultiFuncSCC
    (ip_reg : Amd64Reg)
    (sccAddrs : Array UInt64)
    (blocksByAddr : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (cache : IO.Ref (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))))
    (returnEdges : Std.HashMap UInt64 (Array UInt64))
    (blockToFunc : Std.HashMap UInt64 UInt64)
    (funcBlockAddrs : Std.HashMap UInt64 (Array UInt64))
    (log : String → IO Unit)
    (z3cache : IO.Ref Z3Cache) : IO Unit := do
  let isa := vexSummaryISA Amd64Reg
  -- Identify functions in this SCC
  let mut sccFuncEntrySet : Std.HashSet UInt64 := {}
  for addr in sccAddrs do
    match blockToFunc.get? addr with
    | some fe => sccFuncEntrySet := sccFuncEntrySet.insert fe
    | none => pure ()
  let sccFuncEntries := sccFuncEntrySet.fold (fun acc a => acc.push a) (#[] : Array UInt64)
  -- All function entries (for cross-function call detection)
  let allFuncEntries : Std.HashSet UInt64 := blockToFunc.fold (fun s _ v => s.insert v) {}
  let funcSummaries ← IO.mkRef ({} : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
  log s!"  Multi-func SCC: {sccAddrs.size} blocks across {sccFuncEntries.size} functions"
  for outerRound in List.range 20 do
    let prevSummaries ← funcSummaries.get
    -- Per-function stabilization with cache-aware split (flat, no recursive WTO)
    for funcEntry in sccFuncEntries do
      let funcBlocks := funcBlockAddrs.getD funcEntry #[]
      let cacheContents ← cache.get
      let funcSums ← funcSummaries.get
      -- Collect full function body
      let mut funcBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
      for addr in funcBlocks do
        for b in blocksByAddr.getD addr #[] do
          funcBody := funcBody.push b
      -- Cache-aware split
      let mut convergenceBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
      let mut seeds : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
      let mut exitBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
      for b in funcBody do
        match extractRipTarget ip_reg b.sub with
        | some target =>
          if allFuncEntries.contains target then
            -- Cross-function call
            let summary := if sccFuncEntrySet.contains target
              then funcSums.get? target  -- SCC peer: use funcSummaries
              else cacheContents.get? target  -- external: use cache
            match summary with
            | some sumBranches =>
              for cb in sumBranches do
                let composed := b.compose isa cb
                match simplifyBranch composed with
                | none => pure ()
                | some b' => seeds := seeds.push b'
            | none => exitBranches := exitBranches.push b
          else
            -- Intra-function target: check cache
            match cacheContents.get? target with
            | some cached =>
              -- Pre-converged by inner WTO: compose → seeds
              for cb in cached do
                let composed := b.compose isa cb
                match simplifyBranch composed with
                | none => pure ()
                | some b' => seeds := seeds.push b'
            | none =>
              -- Not cached: convergence body
              convergenceBody := convergenceBody.push b
        | none => exitBranches := exitBranches.push b
      -- closureBody = ALL function body branches (for closure PC extraction)
      let closureBody := funcBody
      let frontier := seeds ++ exitBranches
      log s!"    func 0x{String.mk (Nat.toDigits 16 funcEntry.toNat)} round {outerRound}: {convergenceBody.size} body, {seeds.size} seeds, {exitBranches.size} exits"
      match ← computeFunctionStabilization ip_reg convergenceBody 200 log z3cache
               (initialFrontier := frontier) (closureBody := closureBody) with
      | some (k, result) =>
        funcSummaries.modify (·.insert funcEntry result)
        cache.modify (·.insert funcEntry result)
      | none => log s!"    func 0x{String.mk (Nat.toDigits 16 funcEntry.toNat)}: DID NOT CONVERGE"
    -- Outer convergence check
    let newSummaries ← funcSummaries.get
    let mut changed := false
    for fe in sccFuncEntries do
      let prev := prevSummaries.getD fe #[]
      let curr := newSummaries.getD fe #[]
      if prev.size != curr.size then changed := true
    unless changed do
      log s!"  Multi-func SCC converged after {outerRound + 1} outer rounds"
      break

/-- Dispatch a WTO component: vertex → DAG block, component → SCC fixpoint.
    Single-function SCCs process children first (Bourdoncle order: inner loops
    converge before outer), then run processSCCStabilization which uses cache-aware
    splitting to treat pre-converged inner blocks as seeds.
    Multi-function SCCs use processMultiFuncSCC with outer function-summary loop. -/
partial def processWTOComponent
    (ip_reg : Amd64Reg)
    (blocksByAddr : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (cache : IO.Ref (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))))
    (returnEdges : Std.HashMap UInt64 (Array UInt64))
    (log : String → IO Unit)
    (z3cache : IO.Ref Z3Cache)
    (blockToFunc : Std.HashMap UInt64 UInt64)
    (funcBlockAddrs : Std.HashMap UInt64 (Array UInt64))
    (comp : WTOComponent) : IO Unit := do
  match comp with
  | .vertex addr =>
    processDAGBlock ip_reg addr blocksByAddr cache returnEdges log
  | .component head children =>
    let mut allAddrs : Array UInt64 := #[head]
    for child in children do
      allAddrs := allAddrs ++ child.addrs
    -- Check if this SCC spans multiple functions
    let mut funcEntrySet : Std.HashSet UInt64 := {}
    for addr in allAddrs do
      match blockToFunc.get? addr with
      | some fe => funcEntrySet := funcEntrySet.insert fe
      | none => pure ()
    if funcEntrySet.size > 1 then
      processMultiFuncSCC ip_reg allAddrs blocksByAddr cache returnEdges
        blockToFunc funcBlockAddrs log z3cache
    else
      -- Single-function SCC: process children first (Bourdoncle order),
      -- then stabilize. Inner loops converge → cache populated → cache-aware
      -- split in processSCCStabilization treats them as pre-computed seeds.
      for child in children do
        processWTOComponent ip_reg blocksByAddr cache returnEdges log z3cache
          blockToFunc funcBlockAddrs child
      processSCCStabilization ip_reg allAddrs blocksByAddr cache returnEdges log z3cache blockToFunc

end -- mutual

/-- Unified WTO fixpoint: one WTO over all blocks.
    Parses all function blocks, builds a unified CFG, computes Bourdoncle WTO,
    then processes components in order. DAG blocks get single-pass composition;
    SCC blocks get iterative convergence. -/
def wtoFixpoint
    (functions : Array FunctionSpec)
    (log : String → IO Unit) :
    IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  -- Step 1: Parse ALL function blocks → blocksByAddr
  let mut blocksByAddr : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  let mut allBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
  let mut totalBlocks : Nat := 0
  -- funcBlockAddrs: maps each block addr → all block addrs in the same function
  -- (used for indirect jump edges in CFG)
  let mut funcBlockAddrsBuilder : Array (Array UInt64) := #[]
  -- blockToFunc: maps each block addr → its function's entry addr
  -- (used for return edge computation)
  let mut blockToFunc : Std.HashMap UInt64 UInt64 := {}
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error e =>
      log s!"  PARSE ERROR for {func.name}: {e}"
      return {}
    | .ok pairs =>
      let body := flatBodyDenot ip_reg pairs
      let bodyArr := finsetToArray body
      -- Collect all rip-guard addresses for this function
      let mut funcAddrs : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRipGuard ip_reg b.pc with
        | some addr => funcAddrs := funcAddrs.insert addr
        | none => pure ()
      let funcAddrArr := funcAddrs.fold (fun acc a => acc.push a) (#[] : Array UInt64)
      funcBlockAddrsBuilder := funcBlockAddrsBuilder.push funcAddrArr
      -- Build blockToFunc for this function
      for addr in funcAddrArr do
        blockToFunc := blockToFunc.insert addr func.entryAddr
      -- Group by rip-guard address (source block)
      for b in bodyArr do
        match extractRipGuard ip_reg b.pc with
        | some addr =>
          let arr := blocksByAddr.getD addr #[]
          blocksByAddr := blocksByAddr.insert addr (arr.push b)
        | none => pure ()
        allBody := allBody.push b
      totalBlocks := totalBlocks + pairs.length
      log s!"  {func.name} @ 0x{String.mk (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches"
  log s!"  Total: {totalBlocks} blocks, {allBody.size} body branches, {blocksByAddr.size} source addresses"
  -- Build funcBlockAddrs: each block addr → all sibling block addrs in same function
  let mut funcBlockAddrs : Std.HashMap UInt64 (Array UInt64) := {}
  for funcAddrArr in funcBlockAddrsBuilder do
    for addr in funcAddrArr do
      funcBlockAddrs := funcBlockAddrs.insert addr funcAddrArr
  -- Step 2: Build unified CFG + compute WTO
  let cfgSuccsDirect := buildCFGSuccessors ip_reg allBody funcBlockAddrs
  let mut directEdges : Nat := 0
  for (_, tgts) in cfgSuccsDirect do
    directEdges := directEdges + tgts.size
  log s!"  CFG (direct): {cfgSuccsDirect.size} source blocks, {directEdges} edges"
  -- Step 2b: Compute return edges (call/ret interprocedural linkage)
  log s!"\n=== Return Edge Analysis ==="
  let returnEdges ← buildReturnEdges ip_reg #[.rsp, .rbp] .rsp allBody blockToFunc log
  -- Merge return edges into CFG
  let mut cfgSuccs := cfgSuccsDirect
  for (src, tgts) in returnEdges do
    let mut existing := cfgSuccs.getD src #[]
    for tgt in tgts do
      unless existing.contains tgt do
        existing := existing.push tgt
    cfgSuccs := cfgSuccs.insert src existing
  let mut totalEdges : Nat := 0
  for (_, tgts) in cfgSuccs do
    totalEdges := totalEdges + tgts.size
  log s!"  CFG (with return edges): {cfgSuccs.size} source blocks, {totalEdges} edges"
  -- DFS entries: function entries FIRST, then remaining block addresses.
  -- Ordering matters: function entries must be visited first so that cross-function
  -- edges (e.g., term→paren_expr→expr→sum→term) are discovered during DFS
  -- tree-edge traversal, enabling back-edge detection for inter-function SCCs.
  -- Remaining block addresses are added as fallback roots for blocks unreachable
  -- from any function entry (due to indirect jumps without constant targets).
  let mut entryAddrs : Array UInt64 := functions.map (·.entryAddr)
  let mut entrySet : Std.HashSet UInt64 := {}
  for a in entryAddrs do entrySet := entrySet.insert a
  -- Add all block addresses not already in entryAddrs
  for (addr, _) in blocksByAddr do
    unless entrySet.contains addr do
      entryAddrs := entryAddrs.push addr
      entrySet := entrySet.insert addr
  let wto ← computeWTO entryAddrs cfgSuccs
  let (dagCountAll, sccCount) := wtoStats wto
  let (dagCountTop, sccCountTop) := wtoTopLevelStats wto
  let uniqueAddrs := wtoUniqueAddrs wto
  log s!"  WTO: {uniqueAddrs.size} unique addresses, {dagCountTop} top-level DAGs + {sccCountTop} top-level SCCs"
  log s!"  WTO (recursive): {dagCountAll} DAG vertices at all nesting levels, {sccCount} total SCC components"
  log s!"  WTO: blocksByAddr has {blocksByAddr.size} addresses"
  -- Verify: every blocksByAddr key should appear in WTO
  let mut missingFromWTO : Nat := 0
  for (addr, _) in blocksByAddr do
    unless uniqueAddrs.contains addr do
      missingFromWTO := missingFromWTO + 1
      log s!"    WARNING: block 0x{String.mk (Nat.toDigits 16 addr.toNat)} in blocksByAddr but NOT in WTO"
  let mut extraInWTO : Nat := 0
  for addr in uniqueAddrs do
    unless blocksByAddr.contains addr do
      extraInWTO := extraInWTO + 1
  log s!"  WTO coverage: {missingFromWTO} blocks missing from WTO, {extraInWTO} WTO addrs not in blocksByAddr"
  -- Detailed SCC logging
  log s!"\n=== WTO SCC Details ==="
  ppWTODetailed log wto
  -- Step 3: Process components in block-level WTO order.
  -- Return edges are threaded through so processDAGBlock and processSCCStabilization
  -- can follow return paths (non-constant rip) by composing with continuation blocks.
  let cache ← IO.mkRef ({} : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
  let z3cache ← IO.mkRef ({} : Z3Cache)
  log s!"\n=== WTO Processing ==="
  for comp in wto do
    processWTOComponent ip_reg blocksByAddr cache returnEdges log z3cache blockToFunc funcBlockAddrs comp
  -- Step 3b: Post-WTO function-level summarization
  -- Run computeFunctionStabilization for each function using WTO-populated cache.
  -- For functions whose blocks were fully handled by WTO (DAG or inner SCC),
  -- cache-aware splitting routes all branches to seeds → convergence is trivial.
  log s!"\n=== Post-WTO Function Summarization ==="
  let allFuncEntries : Std.HashSet UInt64 := functions.foldl (fun s f => s.insert f.entryAddr) {}
  for func in functions do
    let funcBlocks := funcBlockAddrs.getD func.entryAddr #[]
    let cacheContents ← cache.get
    -- Collect full function body
    let mut funcBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
    for addr in funcBlocks do
      for b in blocksByAddr.getD addr #[] do
        funcBody := funcBody.push b
    -- Cache-aware split
    let mut convergenceBody : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
    let mut seeds : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
    let mut exitBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
    let isa := vexSummaryISA Amd64Reg
    for b in funcBody do
      match extractRipTarget ip_reg b.sub with
      | some target =>
        if allFuncEntries.contains target then
          -- Cross-function call: compose with cache
          match cacheContents.get? target with
          | some sumBranches =>
            for cb in sumBranches do
              let composed := b.compose isa cb
              match simplifyBranch composed with
              | none => pure ()
              | some b' => seeds := seeds.push b'
          | none => exitBranches := exitBranches.push b
        else
          -- Intra-function target: check cache
          match cacheContents.get? target with
          | some cached =>
            for cb in cached do
              let composed := b.compose isa cb
              match simplifyBranch composed with
              | none => pure ()
              | some b' => seeds := seeds.push b'
          | none =>
            convergenceBody := convergenceBody.push b
      | none => exitBranches := exitBranches.push b
    let closureBody := funcBody
    let frontier := seeds ++ exitBranches
    log s!"  {func.name}: {convergenceBody.size} body, {seeds.size} seeds, {exitBranches.size} exits"
    match ← computeFunctionStabilization ip_reg convergenceBody 200 log z3cache
             (initialFrontier := frontier) (closureBody := closureBody) with
    | some (k, result) =>
      cache.modify (·.insert func.entryAddr result)
      log s!"  {func.name}: converged K={k}, {result.size} branches"
    | none => log s!"  {func.name}: DID NOT CONVERGE"
  -- Step 4: Aggregate per-function summaries from cache
  let cacheContents ← cache.get
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  log s!"\n=== WTO Fixpoint Results ==="
  log s!"  Per-function: all-blocks (entry-only) [old stratified for comparison]"
  let oldCounts := #[("next_sym", 75), ("term", 40), ("sum", 29), ("test", 27),
                      ("expr", 72), ("paren_expr", 67), ("statement", 214)]
  for func in functions do
    -- A function's summary = union of cached branches for all its blocks
    let mut funcBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)) := #[]
    let entryBranches := cacheContents.getD func.entryAddr #[]
    match parseBlocksWithAddresses func.blocks with
    | .error _ => pure ()
    | .ok pairs =>
      for (addr, _) in pairs do
        for b in cacheContents.getD addr #[] do
          funcBranches := funcBranches.push b
    summaries := summaries.insert func.entryAddr funcBranches
    let oldCount := oldCounts.foldl (fun acc (n, c) => if n == func.name then c else acc) 0
    let match_ := if entryBranches.size == oldCount then "MATCH" else "MISMATCH"
    log s!"  {func.name}: {funcBranches.size} ({entryBranches.size}) [old={oldCount}] {match_}"
  -- Z3 cache summary
  let z3cacheContents ← z3cache.get
  log s!"\n=== Z3 Cache Summary ==="
  log s!"  cache entries: {z3cacheContents.size}"
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
  -- Unified WTO fixpoint: one WTO over all blocks
  log "=== Unified WTO Dispatch Loop Stabilization ==="
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
  let _summaries ← wtoFixpoint functions log
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
