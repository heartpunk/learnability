import Instances.ISAs.VexCompTree
import Instances.ISAs.VexProofCompression
import Instances.ISAs.VexIRParser
import Instances.ISAs.ElfSymbolTable
import Instances.ISAs.AntiUnify
import Lean.Data.Json

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
def SymPC.simplifyConst {Reg : Type} : SymPC Reg → Option (SymPC Reg)
  | .true => some .true
  | .eq (.const a) (.const b) => if a == b then some .true else none
  | .lt (.const a) (.const b) => if a < b then some .true else none
  | .le (.const a) (.const b) => if a ≤ b then some .true else none
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
- If addr and addr' are in different memory regions: skip the store
- Otherwise: keep as-is (can't determine statically)

This is an EXACT optimization — it evaluates what the concrete semantics would
compute, just at the symbolic level. No information is lost. Combined with
simplifyConst (which handles const-const comparisons), this collapses the
expression chains that cause unbounded growth in iterative composition.

The region-based elimination uses ELF section layout from CLE: addresses in
different sections (text, data, bss, extern, stack) can't alias. The classifier
maps constant addresses to their section by range lookup, and register-relative
addresses (rsp±k, rbp±k) to a synthetic "stack" region.  Non-overlapping by
CLE's loader construction + x86-64 ABI stack placement. -/

/-- A memory region from the ELF binary (loaded via CLE). -/
structure MemRegion where
  name : String
  vaddr : UInt64
  size : Nat
  flags : String
  deriving Repr, Inhabited

/-- Region identity for non-aliasing: if two addresses have different
    `RegionTag`s, they can't alias. `loaded idx` = ELF section at index `idx`
    in the regions array. `stack` = rsp/rbp-relative (not in any loaded region). -/
inductive RegionTag where
  | loaded (idx : Nat) : RegionTag
  | stack : RegionTag
  deriving DecidableEq, Repr

/-- Look up which loaded region (if any) contains address `c`. -/
def lookupRegion (regions : Array MemRegion) (c : UInt64) : Option RegionTag :=
  let rec go (i : Nat) : Option RegionTag :=
    if i ≥ regions.size then none
    else
      let r := regions[i]!
      if c ≥ r.vaddr && c.toNat < r.vaddr.toNat + r.size then
        some (.loaded i)
      else go (i + 1)
  go 0

/-- Classify a symbolic address into its memory region, if determinable.
    Returns `none` for addresses that can't be classified (conservative).

    Handles indirect loads through base memory: `load(base_mem, const)` where
    the constant is in a loaded ELF region (GOT, data, etc.) classifies as
    `loaded` — the loaded pointer targets the loaded image, not the stack.
    Sound on x86-64: statically-initialized pointers (GOT entries, data section
    pointers) don't point into the runtime stack. -/
def classifyAddr {Reg : Type} [DecidableEq Reg]
    (regions : Array MemRegion) (stackRegs : List Reg)
    (addr : SymExpr Reg) : Option RegionTag :=
  match addr with
  | .const c => lookupRegion regions c
  | .reg r =>
    if stackRegs.any (· == r) then some .stack else none
  | .add64 (.reg r) (.const _) =>
    if stackRegs.any (· == r) then some .stack else none
  | .sub64 (.reg r) (.const _) =>
    if stackRegs.any (· == r) then some .stack else none
  | .load _ _mem (.const c) =>
    -- Indirect load at a constant address through ANY memory state.
    -- If the constant address is in a loaded region (GOT, data, etc.),
    -- the loaded pointer targets the loaded image — not the stack.
    -- Sound because: loaded-region addresses are in read-only sections
    -- (GOT, .rodata, .data). Stack stores don't affect these addresses
    -- (different regions by ELF layout). So load(store_chain, GOT_addr)
    -- returns the same value as load(base_mem, GOT_addr).
    -- This handles the common pattern where the memory has been modified
    -- by stack stores (e.g., store_64(base_mem, rbp-16, rax)) but the
    -- load targets a GOT/data constant that is unaffected.
    lookupRegion regions c
  | _ => none

/-- Optional address classifier. When provided, enables region-based
    store elimination in `resolveLoadFrom`. -/
abbrev AddrClassifier (Reg : Type) := SymExpr Reg → Option RegionTag

/-! ## Expression Diagnostics -/

mutual
def exprNodeCount {Reg : Type} : SymExpr Reg → Nat
  | .const _ => 1
  | .reg _ => 1
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x | .not64 x | .not32 x => 1 + exprNodeCount x
  | .sub32 a b | .shl32 a b | .and32 a b | .or32 a b | .xor32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b =>
    1 + exprNodeCount a + exprNodeCount b
  | .load _ m addr => 1 + memNodeCount m + exprNodeCount addr

def memNodeCount {Reg : Type} : SymMem Reg → Nat
  | .base => 1
  | .store _ m addr val => 1 + memNodeCount m + exprNodeCount addr + exprNodeCount val

def exprUnresolvedLoads {Reg : Type} : SymExpr Reg → Nat
  | .const _ | .reg _ => 0
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x | .not64 x | .not32 x => exprUnresolvedLoads x
  | .sub32 a b | .shl32 a b | .and32 a b | .or32 a b | .xor32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b =>
    exprUnresolvedLoads a + exprUnresolvedLoads b
  | .load _ m addr => (match m with | .base => 0 | _ => 1) + memUnresolvedLoads m + exprUnresolvedLoads addr

def memUnresolvedLoads {Reg : Type} : SymMem Reg → Nat
  | .base => 0
  | .store _ m addr val => memUnresolvedLoads m + exprUnresolvedLoads addr + exprUnresolvedLoads val

def exprSummary {Reg : Type} [ToString Reg] : SymExpr Reg → Nat → String
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
  | .and32 a b, d => s!"and32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .or32 a b, d => s!"or32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .xor32 a b, d => s!"xor32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .mul64 a b, d => s!"mul64({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .not64 a, d => s!"not64({exprSummary a (d-1)})"
  | .sar64 a b, d => s!"sar64({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .sar32 a b, d => s!"sar32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .not32 a, d => s!"not32({exprSummary a (d-1)})"
  | .mul32 a b, d => s!"mul32({exprSummary a (d-1)},{exprSummary b (d-1)})"
  | .load w m addr, d => s!"ld{w.byteCount*8}(mem[{memNodeCount m}],{exprSummary addr (d-1)})"
end

/-- Fold nested add64/sub64 with constants.
    Normalizes stack arithmetic so load/store addresses match.
    e.g. add64(add64(x, C(8)), C(8)) → add64(x, C(16))
         sub64(sub64(x, C(8)), C(16)) → sub64(x, C(24))
         sub64(add64(x, C(16)), C(8)) → add64(x, C(8)) -/
def foldAdd64 {Reg : Type} [DecidableEq Reg]
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

def foldSub64 {Reg : Type} [DecidableEq Reg]
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

/-- Fold `and64` with constant identities and absorption. -/
def foldAnd64 {Reg : Type} [DecidableEq Reg]
    (a b : SymExpr Reg) : SymExpr Reg :=
  match a, b with
  | .const x, .const y => .const (x &&& y)
  | x, .const m =>
    if m == 0xFFFF_FFFF_FFFF_FFFF then x
    else if m == 0 then .const 0
    else .and64 x (.const m)
  | .const m, x =>
    if m == 0xFFFF_FFFF_FFFF_FFFF then x
    else if m == 0 then .const 0
    else .and64 (.const m) x
  | _, _ => .and64 a b

/-- Resolve a load from a (simplified) memory term.
    Walks the store chain looking for a matching address.
    When an `AddrClassifier` is provided, uses region-based non-aliasing to
    skip stores whose address is in a different region from the load address. -/
def resolveLoadFrom {Reg : Type} [DecidableEq Reg]
    (loadWidth : Width) (mem : SymMem Reg) (loadAddr : SymExpr Reg)
    (classify : Option (AddrClassifier Reg) := none) : SymExpr Reg :=
  match mem with
  | .base => .load loadWidth .base loadAddr
  | .store storeWidth innerMem storeAddr storeVal =>
    if loadWidth == storeWidth && loadAddr == storeAddr then
      .and64 storeVal (.const loadWidth.mask)  -- MATCH: truncate to width (read truncates)
    else
      match (storeAddr, loadAddr) with
      | (.const a, .const b) =>
        -- Skip store only when byte ranges are provably non-overlapping.
        -- Range [a, a+sw) and [b, b+lw) don't overlap iff a+sw ≤ b ∨ b+lw ≤ a.
        -- Uses Nat arithmetic with non-wrapping guards to avoid UInt64 wrapping
        -- unsoundness (UInt64 addition wraps mod 2^64, so a + sw ≤ b can hold
        -- vacuously when a is near UInt64.max).
        if a.toNat + storeWidth.byteCount ≤ UInt64.size ∧
           b.toNat + loadWidth.byteCount ≤ UInt64.size ∧
           (a.toNat + storeWidth.byteCount ≤ b.toNat ∨
            b.toNat + loadWidth.byteCount ≤ a.toNat) then
          resolveLoadFrom loadWidth innerMem loadAddr classify  -- non-overlapping, skip store
        else
          .load loadWidth mem loadAddr  -- overlapping or wrapping, keep as-is
      | _ =>
        -- Non-constant addresses that don't match syntactically.
        -- Try region-based non-aliasing: if store and load addresses are in
        -- different regions, they can't alias — skip the store.
        match classify with
        | some clf =>
          -- Constant-vs-stack non-aliasing: a constant (link-time) address
          -- can never alias a stack (runtime rsp/rbp-relative) address.
          let constStackSkip :=
            match loadAddr with
            | .const _ =>
              match clf storeAddr with
              | some .stack => true
              | _ => false
            | _ => false
          let stackConstSkip :=
            match storeAddr with
            | .const _ =>
              match clf loadAddr with
              | some .stack => true
              | _ => false
            | _ => false
          if constStackSkip || stackConstSkip then
            resolveLoadFrom loadWidth innerMem loadAddr classify  -- const/stack non-aliasing
          else
            match (clf storeAddr, clf loadAddr) with
            | (some sr, some lr) =>
              if sr != lr then
                resolveLoadFrom loadWidth innerMem loadAddr classify  -- different regions, skip
              else
                .load loadWidth mem loadAddr  -- same region, can't determine
            | _ => .load loadWidth mem loadAddr  -- unclassifiable, conservative
        | none => .load loadWidth mem loadAddr  -- no classifier, conservative

mutual
/-- Simplify: load-after-store resolution + arithmetic constant folding. -/
def simplifyLoadStoreExpr {Reg : Type} [DecidableEq Reg] : SymExpr Reg → SymExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (simplifyLoadStoreExpr x)
  | .uext32 x => .uext32 (simplifyLoadStoreExpr x)
  | .sext8to32 x => .sext8to32 (simplifyLoadStoreExpr x)
  | .sext32to64 x => .sext32to64 (simplifyLoadStoreExpr x)
  | .not64 x => .not64 (simplifyLoadStoreExpr x)
  | .not32 x => .not32 (simplifyLoadStoreExpr x)
  | .sub32 a b => .sub32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .and32 a b => .and32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)  | .shl32 a b => .shl32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .or32 a b => .or32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .xor32 a b => .xor32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .add64 a b => foldAdd64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .sub64 a b => foldSub64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .xor64 a b => .xor64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .and64 a b => foldAnd64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .or64 a b => .or64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .shl64 a b => .shl64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => .shr64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .load w mem addr =>
    let addr' := simplifyLoadStoreExpr addr
    let mem' := simplifyLoadStoreMem mem
    resolveLoadFrom w mem' addr'

/-- Simplify store chains in a SymMem. -/
def simplifyLoadStoreMem {Reg : Type} [DecidableEq Reg] : SymMem Reg → SymMem Reg
  | .base => .base
  | .store w mem addr val =>
    let mem' := simplifyLoadStoreMem mem
    let addr' := simplifyLoadStoreExpr addr
    let val' := simplifyLoadStoreExpr val
    -- Dead store elimination: if inner memory is a store at the same address
    -- with the same width, the inner store is overwritten — skip it.
    match mem' with
    | .store w' innerMem storeAddr' _ =>
      if w == w' && addr' == storeAddr' then
        .store w innerMem addr' val'
      else
        .store w mem' addr' val'
    | _ => .store w mem' addr' val'
end

/-- Simplify load-after-store patterns in a SymPC. -/
def simplifyLoadStorePC {Reg : Type} [DecidableEq Reg] : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq a b => .eq (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .lt a b => .lt (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .le a b => .le (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .and φ ψ => .and (simplifyLoadStorePC φ) (simplifyLoadStorePC ψ)
  | .not φ => .not (simplifyLoadStorePC φ)

/-! ## Region-Aware Simplification

Variants of the load-after-store simplifier that accept an address classifier
for region-based store elimination. When a store address and load address are
in different memory regions, the store can be skipped (non-aliasing by
construction from ELF section layout). -/

mutual
/-- Region-aware simplify: load-after-store + arithmetic + region non-aliasing. -/
def simplifyLoadStoreExprR {Reg : Type} [DecidableEq Reg]
    (classify : AddrClassifier Reg) : SymExpr Reg → SymExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (simplifyLoadStoreExprR classify x)
  | .uext32 x => .uext32 (simplifyLoadStoreExprR classify x)
  | .sext8to32 x => .sext8to32 (simplifyLoadStoreExprR classify x)
  | .sext32to64 x => .sext32to64 (simplifyLoadStoreExprR classify x)
  | .not64 x => .not64 (simplifyLoadStoreExprR classify x)
  | .not32 x => .not32 (simplifyLoadStoreExprR classify x)
  | .sub32 a b => .sub32 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .and32 a b => .and32 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)  | .shl32 a b => .shl32 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .or32 a b => .or32 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .xor32 a b => .xor32 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .add64 a b => foldAdd64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .sub64 a b => foldSub64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .xor64 a b => .xor64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .and64 a b => foldAnd64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .or64 a b => .or64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .shl64 a b => .shl64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => .shr64 (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .load w mem addr =>
    let addr' := simplifyLoadStoreExprR classify addr
    let mem' := simplifyLoadStoreMemR classify mem
    resolveLoadFrom w mem' addr' (some classify)

/-- Region-aware store chain simplification. -/
def simplifyLoadStoreMemR {Reg : Type} [DecidableEq Reg]
    (classify : AddrClassifier Reg) : SymMem Reg → SymMem Reg
  | .base => .base
  | .store w mem addr val =>
    let mem' := simplifyLoadStoreMemR classify mem
    let addr' := simplifyLoadStoreExprR classify addr
    let val' := simplifyLoadStoreExprR classify val
    -- Dead store elimination: if inner memory is a store at the same address
    -- with the same width, the inner store is overwritten — skip it.
    match mem' with
    | .store w' innerMem storeAddr' _ =>
      if w == w' && addr' == storeAddr' then
        .store w innerMem addr' val'
      else
        .store w mem' addr' val'
    | _ => .store w mem' addr' val'
end

/-- Region-aware PC simplification. -/
def simplifyLoadStorePCR {Reg : Type} [DecidableEq Reg]
    (classify : AddrClassifier Reg) : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq a b => .eq (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .lt a b => .lt (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .le a b => .le (simplifyLoadStoreExprR classify a) (simplifyLoadStoreExprR classify b)
  | .and φ ψ => .and (simplifyLoadStorePCR classify φ) (simplifyLoadStorePCR classify ψ)
  | .not φ => .not (simplifyLoadStorePCR classify φ)

/-- Simplify a PC using region-aware simplification if a classifier is available,
    otherwise fall back to standard simplification. -/
def simplifyLoadStorePCOpt {Reg : Type} [DecidableEq Reg]
    (classify : Option (AddrClassifier Reg)) (pc : SymPC Reg) : SymPC Reg :=
  match classify with
  | some clf => simplifyLoadStorePCR clf pc
  | none => simplifyLoadStorePC pc

/-- Full simplification: load-after-store + constant folding on a branch.
    Returns `none` if the PC is unsatisfiable after simplification. -/
def simplifyBranchFull {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (b : Branch (SymSub Reg) (SymPC Reg))
    (classify : Option (AddrClassifier Reg) := none) :
    Option (Branch (SymSub Reg) (SymPC Reg)) :=
  match classify with
  | some clf =>
    -- Region-aware simplification
    let simplifiedSub : SymSub Reg := {
      regs := fun r => simplifyLoadStoreExprR clf (b.sub.regs r)
      mem := simplifyLoadStoreMemR clf b.sub.mem
    }
    let simplifiedPC := simplifyLoadStorePCR clf b.pc
    match SymPC.simplifyConst simplifiedPC with
    | none => none
    | some pc' => some ⟨simplifiedSub, pc'⟩
  | none =>
    -- Standard simplification (no region info)
    let simplifiedSub : SymSub Reg := {
      regs := fun r => simplifyLoadStoreExpr (b.sub.regs r)
      mem := simplifyLoadStoreMem b.sub.mem
    }
    let simplifiedPC := simplifyLoadStorePC b.pc
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

We use CVC5 (QF_UFBV theory) for exact semantic implication checking:
  stronger → weaker  ⟺  (stronger ∧ ¬weaker) is UNSAT
Queries are batched into a single CVC5 invocation per sub-hash group using
push/pop for efficiency. -/

/-- Collect the top-level conjuncts of a PC into a list. -/
def SymPC.conjuncts {Reg : Type} : SymPC Reg → List (SymPC Reg)
  | .and φ ψ => SymPC.conjuncts φ ++ SymPC.conjuncts ψ
  | pc => [pc]

/-- Collect all atomic comparison PCs from a SymPC (leaf-level eq/lt/le,
    ignoring and/not structure). Used by `semClosed_of_liftedAtomsInBasis`. -/
def SymPC.atoms {Reg : Type} : SymPC Reg → List (SymPC Reg)
  | .true => []
  | .eq l r => [.eq l r]
  | .lt l r => [.lt l r]
  | .le l r => [.le l r]
  | .and φ ψ => SymPC.atoms φ ++ SymPC.atoms ψ
  | .not φ => SymPC.atoms φ

/-! ## PC Expression Canonicalization (Kuznetsov et al. 2012)

Normalizes SymExpr/SymPC so that syntactically different but semantically
equivalent expressions hash identically. Applied in `computePCSignature`
before conjunct comparison, strengthening the syntactic fast-path so the SMT
solver is only invoked for genuinely novel signatures. -/

mutual
/-- Canonicalize a SymExpr: sort operands of commutative ops by hash. -/
def canonicalizeExpr {Reg : Type} [Hashable Reg] : SymExpr Reg → SymExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (canonicalizeExpr x)
  | .uext32 x => .uext32 (canonicalizeExpr x)
  | .sext8to32 x => .sext8to32 (canonicalizeExpr x)
  | .sext32to64 x => .sext32to64 (canonicalizeExpr x)
  | .not64 x => .not64 (canonicalizeExpr x)
  | .not32 x => .not32 (canonicalizeExpr x)
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
  | .and32 a b => .and32 (canonicalizeExpr a) (canonicalizeExpr b)  | .shl32 a b => .shl32 (canonicalizeExpr a) (canonicalizeExpr b)
  | .or32 a b => .or32 (canonicalizeExpr a) (canonicalizeExpr b)
  | .xor32 a b => .xor32 (canonicalizeExpr a) (canonicalizeExpr b)
  | .shl64 a b => .shl64 (canonicalizeExpr a) (canonicalizeExpr b)
  | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => .shr64 (canonicalizeExpr a) (canonicalizeExpr b)
  | .load w m addr => .load w (canonicalizeMem m) (canonicalizeExpr addr)
/-- Canonicalize a SymMem: normalize expressions within stores. -/
def canonicalizeMem {Reg : Type} [Hashable Reg] : SymMem Reg → SymMem Reg
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
def canonicalizePC {Reg : Type} [Hashable Reg] : SymPC Reg → SymPC Reg
  | .true => .true
  | .eq a b =>
    let a' := canonicalizeExpr a; let b' := canonicalizeExpr b
    if (hash a') < (hash b') then .eq a' b' else .eq b' a'
  | .lt a b => .lt (canonicalizeExpr a) (canonicalizeExpr b)
  | .le a b => .le (canonicalizeExpr a) (canonicalizeExpr b)
  | .not (.not x) => canonicalizePC x
  | .not x => .not (canonicalizePC x)
  | .and φ ψ =>
    let φ' := canonicalizePC φ
    let ψ' := canonicalizePC ψ
    let conjuncts := SymPC.conjuncts φ' ++ SymPC.conjuncts ψ'
    let sorted := (conjuncts.toArray.qsort (fun a b => (hash a) < (hash b))).toList
    reassembleAnd sorted

instance : ToString Amd64Reg where
  toString
    | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rsi => "rsi"
    | .rbp => "rbp" | .rsp => "rsp" | .rdi => "rdi" | .rip => "rip"
    | .cc_op => "cc_op" | .cc_dep1 => "cc_dep1" | .cc_dep2 => "cc_dep2" | .cc_ndep => "cc_ndep"
    | .r11 => "r11"
    | .rbx => "rbx"
    | .r8 => "r8"
    | .r9 => "r9"
    | .r12 => "r12"
    | .fs_base => "fs_base"

/-- SMT-LIB2 width suffix for memory operations. -/
def Width.toSMTWidth : Width → String
  | .w8 => "8" | .w16 => "16" | .w32 => "32" | .w64 => "64"

mutual
/-- Encode a SymExpr as an SMT-LIB2 bitvector expression (64-bit). -/
def SymExpr.toSMTLib {Reg : Type} [ToString Reg] : SymExpr Reg → String
  | .const v => s!"(_ bv{v.toNat} 64)"
  | .reg r => s!"reg_{toString r}"
  | .low32 e => s!"((_ zero_extend 32) ((_ extract 31 0) {SymExpr.toSMTLib e}))"
  | .uext32 e => s!"((_ zero_extend 32) ((_ extract 31 0) {SymExpr.toSMTLib e}))"
  | .sext8to32 e => s!"((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) {SymExpr.toSMTLib e})))"
  | .sext32to64 e => s!"((_ sign_extend 32) ((_ extract 31 0) {SymExpr.toSMTLib e}))"
  | .sub32 l r => s!"((_ zero_extend 32) (bvsub ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .shl32 l r => s!"((_ zero_extend 32) (bvshl ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .and32 l r => s!"((_ zero_extend 32) (bvand ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .or32 l r => s!"((_ zero_extend 32) (bvor ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .xor32 l r => s!"((_ zero_extend 32) (bvxor ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .add64 l r => s!"(bvadd {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .sub64 l r => s!"(bvsub {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .xor64 l r => s!"(bvxor {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .and64 l r => s!"(bvand {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .or64 l r => s!"(bvor {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .shl64 l r => s!"(bvshl {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .shr64 l r => s!"(bvlshr {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .mul64 l r => s!"(bvmul {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .not64 e => s!"(bvnot {SymExpr.toSMTLib e})"
  | .sar64 l r => s!"(bvashr {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .sar32 l r => s!"((_ zero_extend 32) (bvashr ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .not32 e => s!"((_ zero_extend 32) (bvnot ((_ extract 31 0) {SymExpr.toSMTLib e})))"
  | .mul32 l r => s!"((_ zero_extend 32) (bvmul ((_ extract 31 0) {SymExpr.toSMTLib l}) ((_ extract 31 0) {SymExpr.toSMTLib r})))"
  | .load w m addr => s!"(load_{Width.toSMTWidth w} {SymMem.toSMTLib m} {SymExpr.toSMTLib addr})"

/-- Encode a SymMem as an SMT-LIB2 expression (uninterpreted sort). -/
def SymMem.toSMTLib {Reg : Type} [ToString Reg] : SymMem Reg → String
  | .base => "base_mem"
  | .store w m addr val =>
    s!"(store_{Width.toSMTWidth w} {SymMem.toSMTLib m} {SymExpr.toSMTLib addr} {SymExpr.toSMTLib val})"
end

/-- Encode a SymPC as an SMT-LIB2 boolean formula.
    Uses unsigned comparison (bvult/bvule) matching evalSymPC semantics. -/
def SymPC.toSMTLib {Reg : Type} [ToString Reg] : SymPC Reg → String
  | .true => "true"
  | .eq l r => s!"(= {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .lt l r => s!"(bvult {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .le l r => s!"(bvule {SymExpr.toSMTLib l} {SymExpr.toSMTLib r})"
  | .and φ ψ => s!"(and {SymPC.toSMTLib φ} {SymPC.toSMTLib ψ})"
  | .not φ => s!"(not {SymPC.toSMTLib φ})"

/-- Collect all register names appearing in a SymPC (for variable declarations). -/
def SymExpr.collectRegNames {Reg : Type} [ToString Reg] [BEq Reg] [Hashable Reg]
    : SymExpr Reg → Std.HashSet String → Std.HashSet String
  | .const _, s => s
  | .reg r, s => s.insert s!"reg_{toString r}"
  | .low32 e, s => SymExpr.collectRegNames e s
  | .uext32 e, s => SymExpr.collectRegNames e s
  | .sext8to32 e, s => SymExpr.collectRegNames e s
  | .sext32to64 e, s => SymExpr.collectRegNames e s
  | .not64 e, s => SymExpr.collectRegNames e s
  | .not32 e, s => SymExpr.collectRegNames e s
  | .sar64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .sar32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .sub32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .shl32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .and32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .or32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .xor32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .add64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .sub64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .xor64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .and64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .or64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .shl64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .shr64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .mul64 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .mul32 l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .load _ _ addr, s => SymExpr.collectRegNames addr s

def SymPC.collectRegNames {Reg : Type} [ToString Reg] [BEq Reg] [Hashable Reg]
    : SymPC Reg → Std.HashSet String → Std.HashSet String
  | .true, s => s
  | .eq l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .lt l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .le l r, s => SymExpr.collectRegNames r (SymExpr.collectRegNames l s)
  | .and φ ψ, s => SymPC.collectRegNames ψ (SymPC.collectRegNames φ s)
  | .not φ, s => SymPC.collectRegNames φ s

mutual
/-- Check if a SymExpr mentions any memory loads. -/
def SymExpr.hasLoad {Reg : Type} : SymExpr Reg → Bool
  | .load _ _ _ => true
  | .const _ | .reg _ => false
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e | .not64 e | .not32 e => SymExpr.hasLoad e
  | .sub32 l r | .shl32 l r | .and32 l r | .or32 l r | .xor32 l r | .add64 l r | .sub64 l r | .xor64 l r
  | .and64 l r | .or64 l r | .shl64 l r | .shr64 l r | .mul64 l r | .mul32 l r | .sar64 l r | .sar32 l r => SymExpr.hasLoad l || SymExpr.hasLoad r

def SymMem.hasLoad {Reg : Type} : SymMem Reg → Bool
  | .base => false
  | .store _ m addr val => SymMem.hasLoad m || SymExpr.hasLoad addr || SymExpr.hasLoad val
end

def SymPC.hasLoad {Reg : Type} : SymPC Reg → Bool
  | .true => false
  | .eq l r | .lt l r | .le l r => SymExpr.hasLoad l || SymExpr.hasLoad r
  | .and φ ψ => SymPC.hasLoad φ || SymPC.hasLoad ψ
  | .not φ => SymPC.hasLoad φ

mutual
/-- Collect all registers referenced in a SymExpr (as Reg values). -/
def SymExpr.collectRegsHS {Reg : Type} [BEq Reg] [Hashable Reg]
    : SymExpr Reg → Std.HashSet Reg → Std.HashSet Reg
  | .const _, s => s
  | .reg r, s => s.insert r
  | .low32 e, s => SymExpr.collectRegsHS e s
  | .uext32 e, s => SymExpr.collectRegsHS e s
  | .sext8to32 e, s => SymExpr.collectRegsHS e s
  | .sext32to64 e, s => SymExpr.collectRegsHS e s
  | .not64 e, s => SymExpr.collectRegsHS e s
  | .not32 e, s => SymExpr.collectRegsHS e s
  | .sar64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .sar32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .sub32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .shl32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .and32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .or32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .xor32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .add64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .sub64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .xor64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .and64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .or64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .shl64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .shr64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .mul64 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .mul32 l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .load _ m addr, s => SymExpr.collectRegsHS addr (SymMem.collectRegsHS m s)

/-- Collect all registers referenced in a SymMem. -/
def SymMem.collectRegsHS {Reg : Type} [BEq Reg] [Hashable Reg]
    : SymMem Reg → Std.HashSet Reg → Std.HashSet Reg
  | .base, s => s
  | .store _ m addr val, s =>
    SymExpr.collectRegsHS val (SymExpr.collectRegsHS addr (SymMem.collectRegsHS m s))
end

/-- Collect all registers referenced in a SymPC. -/
def SymPC.collectRegsHS {Reg : Type} [BEq Reg] [Hashable Reg]
    : SymPC Reg → Std.HashSet Reg → Std.HashSet Reg
  | .true, s => s
  | .eq l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .lt l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .le l r, s => SymExpr.collectRegsHS r (SymExpr.collectRegsHS l s)
  | .and φ ψ, s => SymPC.collectRegsHS ψ (SymPC.collectRegsHS φ s)
  | .not φ, s => SymPC.collectRegsHS φ s

/-- Parse SMT check-sat results from stdout, skipping warnings, blank lines, and
    any other non-result output.  Only lines that are exactly "sat" or "unsat"
    count as results; they are collected in order, so result index i corresponds
    to the i-th check-sat query.  Any query whose result line is absent (e.g.
    because the solver errored) is simply not represented — callers treat missing
    entries conservatively (not-unsat). -/
def parseSMTResults (stdout : String) : Array Bool :=
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

/-! ## SMT Query Cache (Green-style)

Green (Visser et al. 2012) caches solver results by canonicalizing and hashing
the query formula.  On cache hit, the solver call is skipped entirely.

Pipeline: CANONIZE → HASH → CACHE LOOKUP → (miss?) CVC5 → STORE

The cache maps: hash(canonicalizePC(assertion)) → Bool (true = UNSAT).
Implication queries (A → B) are represented as (A ∧ ¬B): UNSAT means A implies B.
Equivalence queries (A ↔ B) are decomposed into two implication queries. -/

/-- SMT query cache: hash of canonicalized assertion formula → UNSAT result. -/
abbrev SMTCache := Std.HashMap UInt64 Bool

/-- Cache key for an implication query "does A imply B?",
    i.e. is (A ∧ ¬B) UNSAT?  Canonicalizes the combined formula
    so semantically identical queries hash the same. -/
def smtImplCacheKey {Reg : Type} [Hashable Reg] (a b : SymPC Reg) : UInt64 :=
  hash (canonicalizePC (.and a (.not b)))

/-- Run a batch of SMT implication queries with caching (backed by CVC5).
    Each query (A, B) checks: is (A ∧ ¬B) UNSAT? (i.e. does A → B?)
    Returns: (results array aligned with input, cache hits count).
    Updates the cache ref with new results. -/
def smtCheckImplCached {Reg : Type} [BEq Reg] [Hashable Reg] [ToString Reg]
    (cache : IO.Ref SMTCache)
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
    let key := smtImplCacheKey a b
    match c.get? key with
    | some v => results := results.set! pairIdx (some v); hits := hits + 1
    | none =>
      missOrigIdx := missOrigIdx.push pairIdx
      missPairs := missPairs.push (a, b)
    pairIdx := pairIdx + 1
  -- Phase 2: batch CVC5 for cache misses
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
      let smtOut ← IO.Process.output { cmd := "cvc5", args := #["--incremental", tmpFile.toString] }
      allMissResults := allMissResults ++ parseSMTResults smtOut.stdout
      chunkStart := chunkEnd
    -- Store results in cache and in output array
    let mut c' ← cache.get
    let mut missIdx : Nat := 0
    for (a, b) in missPairs do
      let isUnsat := if h : missIdx < allMissResults.size then allMissResults[missIdx] else false
      if h2 : missIdx < missOrigIdx.size then
        results := results.set! missOrigIdx[missIdx] (some isUnsat)
      c' := c'.insert (smtImplCacheKey a b) isUnsat
      missIdx := missIdx + 1
    cache.set c'
  -- Phase 3: unwrap
  return (results.map (fun r => r.getD false), hits)

/-! ## Semantic Closedness Witness Finding

Given a set of branches and a closure, find for each (branch, guard) pair
a closure member that is semantically equivalent to the lifted guard.
This is the untrusted CVC5 oracle — witnesses are verified by bv_decide
at build time. CVC5 is NOT in the TCB. -/

/-- Evidence for how a lifted PC relates to the closure. -/
inductive SemClosedWitness where
  | trivialFalse                  -- lifted PC simplified to unsatisfiable
  | trivialTrue                   -- lifted PC simplified to tautology
  | witness (closureIdx : Nat)    -- closure[closureIdx] is semantically equivalent
  | noWitness                     -- no equivalent closure member found (violation)
  deriving Repr, Inhabited

/-- For each (branch, guard) pair, find a closure member semantically equivalent
    to the lifted guard `substSymPC b.sub φ`. Uses CVC5 as an untrusted oracle.

    Returns array of `(branch_idx, guard_idx, evidence)` triples covering all
    `branches.size × closure.size` pairs. The evidence records HOW closedness
    was established:
    - `trivialFalse` / `trivialTrue`: simplified to constant (bv_decide verifies)
    - `witness j`: `closure[j]` is semantically equivalent (bv_decide verifies)
    - `noWitness`: no equivalent found (closedness violation) -/
def findSemClosedWitnesses {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [Hashable Reg] [BEq Reg] [ToString Reg]
    (branches : Array (Branch (SymSub Reg) (SymPC Reg)))
    (closure : Array (SymPC Reg))
    (smtCache : IO.Ref SMTCache)
    (log : String → IO Unit := fun _ => pure ()) :
    IO (Array (Nat × Nat × SemClosedWitness)) := do
  let mut results : Array (Nat × Nat × SemClosedWitness) := #[]
  -- Phase 1: Classify each pair (trivial / syntactic / needs SMT)
  -- smtPCs collects simplified PCs needing SMT; smtMeta tracks their (b_idx, phi_idx)
  let mut smtPCs : Array (SymPC Reg) := #[]
  let mut smtMeta : Array (Nat × Nat) := #[]
  let mut b_idx : Nat := 0
  for b in branches do
    let mut phi_idx : Nat := 0
    for phi in closure do
      let lifted := substSymPC b.sub phi
      let liftedSimplified := simplifyLoadStorePC lifted
      match SymPC.simplifyConst liftedSimplified with
      | none =>
        results := results.push (b_idx, phi_idx, .trivialFalse)
      | some .true =>
        results := results.push (b_idx, phi_idx, .trivialTrue)
      | some pc' =>
        -- Syntactic match against closure
        let mut found := false
        let mut j : Nat := 0
        for phi_j in closure do
          if !found && phi_j == pc' then
            results := results.push (b_idx, phi_idx, .witness j)
            found := true
          j := j + 1
        unless found do
          smtPCs := smtPCs.push pc'
          smtMeta := smtMeta.push (b_idx, phi_idx)
      phi_idx := phi_idx + 1
    b_idx := b_idx + 1
  log s!"  [witnesses] total={branches.size * closure.size} trivial+syntactic={results.size} smt_candidates={smtPCs.size}"
  -- Phase 2: Batch SMT equivalence check for remaining pairs.
  -- For each candidate, check against ALL closure members in one batch.
  -- Equivalence = forward implication + reverse implication.
  if smtPCs.size > 0 then
    let n := closure.size
    let mut allFwdPairs : Array (SymPC Reg × SymPC Reg) := #[]
    let mut allRevPairs : Array (SymPC Reg × SymPC Reg) := #[]
    for pc' in smtPCs do
      for phi_j in closure do
        allFwdPairs := allFwdPairs.push (pc', phi_j)
        allRevPairs := allRevPairs.push (phi_j, pc')
    let (fwdResults, fwdHits) ← smtCheckImplCached smtCache allFwdPairs ".lake/smt_witness.smt2"
    let (revResults, revHits) ← smtCheckImplCached smtCache allRevPairs ".lake/smt_witness.smt2"
    log s!"  [witnesses] smt: {allFwdPairs.size * 2} queries (cache hits={fwdHits + revHits})"
    -- Map results back: candidate i's closure comparisons are at [i*n .. (i+1)*n)
    let mut smtFound : Nat := 0
    for ci in [:smtPCs.size] do
      if h_ci : ci < smtMeta.size then
        let (bi, pi) := smtMeta[ci]
        let base := ci * n
        let mut witnessFound := false
        for j in [:n] do
          if !witnessFound then
            let idx := base + j
            if h1 : idx < fwdResults.size then
              if h2 : idx < revResults.size then
                if fwdResults[idx] && revResults[idx] then
                  results := results.push (bi, pi, .witness j)
                  witnessFound := true
                  smtFound := smtFound + 1
        unless witnessFound do
          results := results.push (bi, pi, .noWitness)
    let violations := smtPCs.size - smtFound
    log s!"  [witnesses] smt_found={smtFound} violations={violations}"
  return results

/-- Prefix all SMT variable names in an SMT-LIB string.
    Replaces `reg_` with `{prefix}reg_` and `base_mem` with `{prefix}base_mem`. -/
def prefixSMTVars (pfx : String) (smt : String) : String :=
  smt.replace "reg_" (pfx ++ "reg_") |>.replace "base_mem" (pfx ++ "base_mem")

/-- Check SemClosed per-pair using two-state CVC5 queries.
    For each lifted PC, checks: if two states agree on all closure PCs,
    do they agree on the lifted PC?

    Query: (closure agreement ∧ lifted disagreement) is UNSAT?
    UNSAT → SemClosed holds for this pair. -/
def smtCheckSemClosedBatch {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    [Hashable Reg] [BEq Reg] [ToString Reg]
    (liftedPCs : Array (SymPC Reg))
    (closure : Array (SymPC Reg))
    (log : String → IO Unit := fun _ => pure ())
    (tmpFile : System.FilePath := ".lake/smt_semclosed.smt2") :
    IO (Array Bool) := do
  if liftedPCs.size == 0 then return #[]
  -- Collect register names from ALL PCs (lifted + closure)
  let mut regNames : Std.HashSet String := {}
  let mut needsMem := false
  for pc in liftedPCs do
    regNames := SymPC.collectRegNames pc regNames
    if SymPC.hasLoad pc then needsMem := true
  for pc in closure do
    regNames := SymPC.collectRegNames pc regNames
    if SymPC.hasLoad pc then needsMem := true
  -- Build two-state preamble: s1_ and s2_ prefixed variables
  let mut preamble := "(set-logic QF_UFBV)\n"
  for name in regNames do
    preamble := preamble ++ s!"(declare-const s1_{name} (_ BitVec 64))\n"
    preamble := preamble ++ s!"(declare-const s2_{name} (_ BitVec 64))\n"
  if needsMem then
    preamble := preamble ++ "(declare-sort Mem 0)\n"
    preamble := preamble ++ "(declare-const s1_base_mem Mem)\n"
    preamble := preamble ++ "(declare-const s2_base_mem Mem)\n"
    for w in ["8", "16", "32", "64"] do
      preamble := preamble ++ s!"(declare-fun load_{w} (Mem (_ BitVec 64)) (_ BitVec 64))\n"
      preamble := preamble ++ s!"(declare-fun store_{w} (Mem (_ BitVec 64) (_ BitVec 64)) Mem)\n"
  -- Build closure agreement assertions (persistent across push/pop)
  let mut agreeAsserts := ""
  for psi in closure do
    let psiSMT := SymPC.toSMTLib psi
    let s1Psi := prefixSMTVars "s1_" psiSMT
    let s2Psi := prefixSMTVars "s2_" psiSMT
    agreeAsserts := agreeAsserts ++ s!"(assert (= {s1Psi} {s2Psi}))\n"
  -- Build incremental script: for each lifted PC, push/assert-disagree/check/pop
  let mut script := preamble ++ agreeAsserts
  for lifted in liftedPCs do
    let liftedSMT := SymPC.toSMTLib lifted
    let s1Lifted := prefixSMTVars "s1_" liftedSMT
    let s2Lifted := prefixSMTVars "s2_" liftedSMT
    script := script ++ "(push)\n"
    script := script ++ s!"(assert (not (= {s1Lifted} {s2Lifted})))\n"
    script := script ++ "(check-sat)\n"
    script := script ++ "(pop)\n"
  script := script ++ "(exit)\n"
  IO.FS.writeFile tmpFile script
  let smtOut ← IO.Process.output { cmd := "cvc5", args := #["--incremental", tmpFile.toString] }
  let results := parseSMTResults smtOut.stdout
  log s!"  [semclosed-smt] {liftedPCs.size} two-state queries, {results.filter id |>.size} pass"
  return results

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

/-- Check h_contains: every branch's PC is determined by the closure.
    Verifies that all top-level conjuncts of each b.pc appear in the closure.
    This is the computational check for the abstract `h_contains` hypothesis
    (see `evalSymPC_of_conjunctsInClosure` in VexPipelineBridge.lean for soundness).
    Returns (allPassed, failureCount, ripMisses, dataMisses). -/
def checkHContains {Reg : Type} [DecidableEq Reg] [BEq Reg] [Hashable (SymPC Reg)]
    (ip_reg : Reg) (branches : Array (Branch (SymSub Reg) (SymPC Reg)))
    (closure : Array (SymPC Reg)) : Bool × Nat × Nat × Nat := Id.run do
  let closureSet : Std.HashSet (SymPC Reg) :=
    closure.foldl (fun s pc => s.insert pc) {}
  let mut ripMisses : Nat := 0
  let mut dataMisses : Nat := 0
  for b in branches do
    for c in SymPC.conjuncts b.pc do
      unless closureSet.contains c do
        if isRipGuardPC ip_reg c then
          ripMisses := ripMisses + 1
        else
          dataMisses := dataMisses + 1
  let total := ripMisses + dataMisses
  return (total == 0, total, ripMisses, dataMisses)

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
  -- catching more syntactic matches before falling through to the SMT solver.
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

/-- Key for PC-signature dedup: combines substitution with PC signature.
    Two branches with the same dedup key are in the same equivalence class.
    Uses structural equality on `sub` (not hash) to avoid hash-collision unsoundness. -/
structure SigDedupKey (Reg : Type) [DecidableEq Reg] [Fintype Reg] where
  sub : SymSub Reg
  sig : List Bool

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : BEq (SigDedupKey Reg) where
  beq k₁ k₂ := decide (k₁.sub = k₂.sub) && k₁.sig == k₂.sig

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] :
    Hashable (SigDedupKey Reg) where
  hash k := mixHash (hash k.sub) (hashPCSignature k.sig)

/-- Dedup an array of branches by (sub, PC-signature) equivalence class.
    Returns (dedupedArray, collapsedCount). -/
def dedupBySignature {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg]
    (closure : Array (SymPC Reg))
    (branches : Array (Branch (SymSub Reg) (SymPC Reg))) :
    Array (Branch (SymSub Reg) (SymPC Reg)) × Nat := Id.run do
  let mut seen : Std.HashSet (SigDedupKey Reg) := {}
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut collapsed : Nat := 0
  for b in branches do
    let sig := computePCSignature closure b.pc
    let key : SigDedupKey Reg := ⟨b.sub, sig⟩
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
    Array (Branch (SymSub Reg) (SymPC Reg) × Nat) × Nat × Nat × Nat := Id.run do
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
  -- Compose using index, tracking which body branch produced each result
  let mut result : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
  let mut dropped : Nat := 0
  let mut composed_count : Nat := 0
  let totalPairs := bodyArr.size * frontierArr.size
  let mut bodyIdx : Nat := 0
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
      | some b' => result := result.push (b', bodyIdx)
    bodyIdx := bodyIdx + 1
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

/-! ## Template extraction and matching for anti-unification-based dedup

When the ground PC closure explodes, anti-unify consecutive-round PCs to
extract templates. PCs that are instances of a known template can be collapsed,
since they represent the same "shape" with different data values (holes). -/

/-- Pair PCs from previous and current frontier by body branch index.
    Groups both arrays by body index, then produces (old, new) pairs
    within each group. Only pairs PCs that share the same body index
    AND the same substitution hash (to avoid pairing unrelated paths). -/
def pairFrontierPCs {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg]
    (previous current : Array (Branch (SymSub Reg) (SymPC Reg) × Nat))
    : Array (SymPC Reg × SymPC Reg) := Id.run do
  -- Build index: bodyIdx → array of PCs (with sub hash for filtering)
  let mut prevByBody : Std.HashMap Nat (Array (SymPC Reg × UInt64)) := {}
  for (b, bodyIdx) in previous do
    let arr := prevByBody.getD bodyIdx #[]
    prevByBody := prevByBody.insert bodyIdx (arr.push (b.pc, hash b.sub))
  let mut pairs : Array (SymPC Reg × SymPC Reg) := #[]
  for (b, bodyIdx) in current do
    let subH := hash b.sub
    if let some prevPCs := prevByBody.get? bodyIdx then
      for (prevPC, prevSubH) in prevPCs do
        -- Only pair PCs from branches with the same sub hash
        if prevSubH == subH && prevPC != b.pc then
          pairs := pairs.push (prevPC, b.pc)
  return pairs

/-- Extract templates from PC pairs via anti-unification.
    Filters trivial (0-hole) results — those are just identical PCs
    and don't help with dedup. -/
def extractTemplatesFromPairs {Reg : Type} [DecidableEq Reg]
    (pairs : Array (SymPC Reg × SymPC Reg))
    : Array (TemplatePC Reg) := Id.run do
  let mut templates : Array (TemplatePC Reg) := #[]
  for (l, r) in pairs do
    let (tpc, _) := VexISA.antiUnify l r
    if tpc.isParametric then
      templates := templates.push tpc
  return templates

mutual
/-- Match a template expression against a ground expression.
    Returns `some bindings` if the ground expression is an instance of the
    template, where `bindings` maps hole IDs to ground sub-expressions.
    Returns `none` on mismatch. -/
def matchTemplateExpr {Reg : Type} [DecidableEq Reg]
    (bindings : Std.HashMap HoleId (SymExpr Reg))
    (t : TemplateExpr Reg) (e : SymExpr Reg)
    : Option (Std.HashMap HoleId (SymExpr Reg)) :=
  match t with
  | .hole h =>
    match bindings.get? h with
    | some existing => if existing == e then some bindings else none
    | none => some (bindings.insert h e)
  | .const v => match e with | .const v' => if v == v' then some bindings else none | _ => none
  | .reg r => match e with | .reg r' => if r == r' then some bindings else none | _ => none
  | .low32 tx => match e with | .low32 ex => matchTemplateExpr bindings tx ex | _ => none
  | .uext32 tx => match e with | .uext32 ex => matchTemplateExpr bindings tx ex | _ => none
  | .sext8to32 tx => match e with | .sext8to32 ex => matchTemplateExpr bindings tx ex | _ => none
  | .sext32to64 tx => match e with | .sext32to64 ex => matchTemplateExpr bindings tx ex | _ => none
  | .sub32 ta tb => match e with
    | .sub32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .shl32 ta tb => match e with
    | .shl32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .and32 ta tb => match e with
    | .and32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .or32 ta tb => match e with
    | .or32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .xor32 ta tb => match e with
    | .xor32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .add64 ta tb => match e with
    | .add64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .sub64 ta tb => match e with
    | .sub64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .xor64 ta tb => match e with
    | .xor64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .and64 ta tb => match e with
    | .and64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .or64 ta tb => match e with
    | .or64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .shl64 ta tb => match e with
    | .shl64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .shr64 ta tb => match e with
    | .shr64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .mul64 ta tb => match e with
    | .mul64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .mul32 ta tb => match e with
    | .mul32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .not64 ta => match e with
    | .not64 ea => matchTemplateExpr bindings ta ea
    | _ => none
  | .sar64 ta tb => match e with
    | .sar64 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .sar32 ta tb => match e with
    | .sar32 ea eb => (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
    | _ => none
  | .not32 ta => match e with
    | .not32 ea => matchTemplateExpr bindings ta ea
    | _ => none
  | .load tw tm ta => match e with
    | .load ew em ea =>
      if tw == ew then
        (matchTemplateMem bindings tm em).bind (matchTemplateExpr · ta ea)
      else none
    | _ => none

/-- Match a template memory against a ground memory. -/
def matchTemplateMem {Reg : Type} [DecidableEq Reg]
    (bindings : Std.HashMap HoleId (SymExpr Reg))
    (t : TemplateMem Reg) (m : SymMem Reg)
    : Option (Std.HashMap HoleId (SymExpr Reg)) :=
  match t, m with
  | .base, .base => some bindings
  | .store tw tm ta tv, .store ew em ea ev =>
    if tw == ew then
      (matchTemplateMem bindings tm em).bind fun b1 =>
      (matchTemplateExpr b1 ta ea).bind fun b2 =>
      matchTemplateExpr b2 tv ev
    else none
  | _, _ => none
end

/-- Match a template PC against a ground PC.
    Returns `some bindings` if the ground PC is an instance of the template. -/
def matchTemplatePC {Reg : Type} [DecidableEq Reg]
    (bindings : Std.HashMap HoleId (SymExpr Reg))
    (t : TemplatePC Reg) (pc : SymPC Reg)
    : Option (Std.HashMap HoleId (SymExpr Reg)) :=
  match t, pc with
  | .true, .true => some bindings
  | .eq ta tb, .eq ea eb =>
    (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
  | .lt ta tb, .lt ea eb =>
    (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
  | .le ta tb, .le ea eb =>
    (matchTemplateExpr bindings ta ea).bind (matchTemplateExpr · tb eb)
  | .and tφ tψ, .and eφ eψ =>
    (matchTemplatePC bindings tφ eφ).bind (matchTemplatePC · tψ eψ)
  | .not tφ, .not eφ => matchTemplatePC bindings tφ eφ
  | _, _ => none

/-- Check if a ground PC matches any known template (is an instance).
    Tries each template in order, returns true on first match. -/
def isTemplateInstance {Reg : Type} [DecidableEq Reg]
    (templates : Array (TemplatePC Reg)) (pc : SymPC Reg) : Bool :=
  templates.any fun t => (matchTemplatePC {} t pc).isSome

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
  let mut sigSeen : Std.HashSet (SigDedupKey Reg) := {}
  let initSig := computePCSignature closure initBranch.pc
  -- initSigKey inserted after closedness check determines dedupSubHash
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[(initBranch, bodyArr.size)]
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
  let initSigKey : SigDedupKey Reg := ⟨initBranch.sub, initSig⟩
  sigSeen := sigSeen.insert initSigKey
  let mut previousFrontier : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
  -- Template-based dedup: activated when explosion is detected
  let mut templates : Array (TemplatePC Reg) := #[]
  let mut templatesActive := false
  let explosionThreshold : Nat := 3  -- trigger when composed > threshold × frontier
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    previousFrontier := frontier
    let (composed, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr (frontier.map (·.1))
    -- Template extraction: detect explosion and extract templates
    let mut templateCollapsed : Nat := 0
    if !templatesActive && previousFrontier.size > 0 &&
       composed.size > explosionThreshold * previousFrontier.size then
      -- Explosion detected: anti-unify consecutive-round PCs to find templates
      let pcPairsForAU := pairFrontierPCs previousFrontier composed
      let newTemplates := extractTemplatesFromPairs pcPairsForAU
      if newTemplates.size > 0 then
        templates := templates ++ newTemplates
        templatesActive := true
        let totalHoles := newTemplates.foldl (fun acc t => acc + t.holeCount) 0
        log s!"    TEMPLATES ACTIVATED: {newTemplates.size} templates, {totalHoles} total holes (explosion: {composed.size} > {explosionThreshold}×{previousFrontier.size})"
    -- Inline dedup: exact-match via HashSet + signature-class via sigSeen
    -- Template dedup runs first when active (before signature dedup)
    let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
    let mut dupes : Nat := 0
    let mut sigCollapsed : Nat := 0
    for (b, bodyIdx) in composed do
      if current.contains b then
        dupes := dupes + 1
      else if templatesActive && isTemplateInstance templates b.pc then
        -- PC matches a known template — collapse (don't add to frontier)
        templateCollapsed := templateCollapsed + 1
      else
        -- Check signature-class dedup (uses projection hash if closed)
        let sig := computePCSignature closure b.pc
        let key : SigDedupKey Reg := ⟨b.sub, sig⟩
        if sigSeen.contains key then
          sigCollapsed := sigCollapsed + 1
        else
          sigSeen := sigSeen.insert key
          newBranches := newBranches.push (b, bodyIdx)
    -- Semantic subsumption via SMT: batch check new branches against existing
    let t_prune_start ← IO.monoMsNow
    let mut prunedCount : Nat := 0
    -- Build (stronger_pc, weaker_pc) pairs and track which new branch each belongs to
    let mut pcPairs : Array (SymPC Reg × SymPC Reg) := #[]
    let mut queryBranchIdx : Array Nat := #[]
    let mut branchIdx : Nat := 0
    for (bi, _) in newBranches do
      let h := hash bi.sub
      let existingGroup := allBranchesBySub.getD h #[]
      for bj in existingGroup do
        if bi.pc != bj.pc then
          pcPairs := pcPairs.push (bi.pc, bj.pc)
          queryBranchIdx := queryBranchIdx.push branchIdx
      branchIdx := branchIdx + 1
    -- Call CVC5 with caching (Green-style)
    let mut subsumedSet : Std.HashSet Nat := {}
    if pcPairs.size > 0 then
      let subsCache ← IO.mkRef ({} : SMTCache)
      let (subsResults, subsHits) ← smtCheckImplCached subsCache pcPairs ".lake/smt_subsumption.smt2"
      for i in [:subsResults.size] do
        if h : i < subsResults.size then
          if subsResults[i] then
            if h2 : i < queryBranchIdx.size then
              subsumedSet := subsumedSet.insert queryBranchIdx[i]
      log s!"    smt: {pcPairs.size} queries, cache_hits={subsHits}, {subsumedSet.size} subsumed"
    -- Filter new branches
    let mut survivingNew : Array (Branch (SymSub Reg) (SymPC Reg) × Nat) := #[]
    branchIdx := 0
    for bi in newBranches do
      if subsumedSet.contains branchIdx then
        prunedCount := prunedCount + 1
      else
        survivingNew := survivingNew.push bi
      branchIdx := branchIdx + 1
    newBranches := survivingNew
    -- Update tracking structures with surviving new branches
    for (b, _) in newBranches do
      current := current.insert b
      let h := hash b.sub
      let arr := allBranchesBySub.getD h #[]
      allBranchesBySub := allBranchesBySub.insert h (arr.push b)
    let t_end ← IO.monoMsNow
    -- Count distinct subs in frontier (diagnostic: how many "paths"?)
    let mut frontierSubs : Std.HashSet UInt64 := {}
    let mut frontierSubsNoRip : Std.HashSet UInt64 := {}
    let mut projectedSubs : Std.HashSet UInt64 := {}
    for (b, _) in newBranches do
      frontierSubs := frontierSubs.insert (hash b.sub)
      let noRipSub : SymSub Reg := { b.sub with regs := fun r => if r == ip_reg then .const 0 else b.sub.regs r }
      frontierSubsNoRip := frontierSubsNoRip.insert (hash noRipSub)
      -- Project sub onto closed projection registers
      projectedSubs := projectedSubs.insert (projHashOf b.sub)
    log s!"  K={k}: |S|={current.size} |frontier|={frontier.size} |new|={newBranches.size} |distinct_subs|={frontierSubs.size} |no_rip|={frontierSubsNoRip.size} |proj|={projectedSubs.size} pairs={pairsComposed} skipped={skipped} dropped={dropped} dupes={dupes} sig_collapsed={sigCollapsed} pruned={prunedCount} templates_active={templatesActive} n_templates={templates.size} template_collapsed={templateCollapsed} compose={t_prune_start - t_start}ms prune={t_end - t_prune_start}ms total={t_end - t_start}ms"
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

/-! ## JSON Block Loading

Load VEX IR blocks from JSON files. Supports two formats:
1. Flat format: `{"arch": "amd64", "blocks": ["IRSB {...}", ...]}`
2. Per-function format: `{"arch": "amd64", "functions": {"name": {"addr": "0x...", "size": N, "blocks": [...]}, ...}}`
The flat format comes from pyvex linear sweep. The per-function format is the
legacy format from `reference/tinyc/parser_nt_blocks.json`. -/

/-- Load a flat list of IRSB strings from a JSON file.
    Accepts both flat format (blocks array) and per-function format (concatenates all blocks). -/
def loadBlocksFromJSON (path : System.FilePath) : IO (Array String) := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => throw (IO.userError s!"JSON parse error in {path}: {e}")
  | .ok json =>
    -- Try flat format first: {"blocks": [...]}
    match json.getObjValAs? (α := Array String) "blocks" with
    | .ok blocks => return blocks
    | .error _ =>
      -- Try per-function format: {"functions": {"name": {"blocks": [...]}}}
      match json.getObjVal? "functions" with
      | .error _ => throw (IO.userError s!"JSON has neither 'blocks' nor 'functions' key")
      | .ok funcsJson =>
        match funcsJson with
        | .obj funcsObj =>
          let mut allBlocks : Array String := #[]
          for (_, funcJson) in funcsObj.toArray do
            match funcJson.getObjValAs? (α := Array String) "blocks" with
            | .ok blocks => allBlocks := allBlocks ++ blocks
            | .error e => throw (IO.userError s!"Error reading function blocks: {e}")
          return allBlocks
        | _ => throw (IO.userError s!"'functions' value is not an object")

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

/-- Parse a hex address string (with or without 0x prefix) to UInt64. -/
private def parseHexAddr (s : String) : Option UInt64 :=
  let digits := if s.startsWith "0x" || s.startsWith "0X" then s.drop 2 else s
  digits.foldl (fun acc c =>
    acc.bind fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (n * 16 + (c.toNat - 'A'.toNat + 10))
      else none) (some 0)
  |>.map UInt64.ofNat

/-- Parse memory regions from JSON array.
    Format: `[{"name": "...", "vaddr": "0x...", "size": N, "flags": "..."}, ...]` -/
private def parseMemRegions (json : Lean.Json) : IO (Array MemRegion) := do
  match json.getArr? with
  | .error e => throw (IO.userError s!"memory_regions is not an array: {e}")
  | .ok arr =>
    let mut regions : Array MemRegion := #[]
    for item in arr do
      let name ← match item.getObjValAs? (α := String) "name" with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"region missing name: {e}")
      let vaddrStr ← match item.getObjValAs? (α := String) "vaddr" with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"region missing vaddr: {e}")
      let vaddr ← match parseHexAddr vaddrStr with
        | some a => pure a
        | none => throw (IO.userError s!"bad region vaddr: {vaddrStr}")
      let size ← match item.getObjValAs? (α := Nat) "size" with
        | .ok n => pure n
        | .error e => throw (IO.userError s!"region missing size: {e}")
      let flags ← match item.getObjValAs? (α := String) "flags" with
        | .ok s => pure s
        | .error _ => pure ""  -- flags optional
      regions := regions.push ⟨name, vaddr, size, flags⟩
    return regions

/-- Load per-function specs from legacy JSON format.
    Format: `{"functions": {"name": {"addr": "0x...", "size": N, "blocks": [...]}, ...},
              "memory_regions": [...]}` -/
def loadFunctionsFromJSON (path : System.FilePath) : IO (Array FunctionSpec × Array MemRegion) := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => throw (IO.userError s!"JSON parse error in {path}: {e}")
  | .ok json =>
    -- Parse memory regions (optional — absent in older JSON files)
    let regions ← match json.getObjVal? "memory_regions" with
      | .ok regionsJson => parseMemRegions regionsJson
      | .error _ => pure #[]
    match json.getObjVal? "functions" with
    | .error _ => throw (IO.userError s!"JSON has no 'functions' key (not per-function format)")
    | .ok funcsJson =>
      match funcsJson with
      | .obj funcsObj =>
        let mut specs : Array FunctionSpec := #[]
        for (name, funcJson) in funcsObj.toArray do
          let addrStr ← match funcJson.getObjValAs? (α := String) "addr" with
            | .ok s => pure s
            | .error e => throw (IO.userError s!"Missing addr for {name}: {e}")
          let addr ← match parseHexAddr addrStr with
            | some a => pure a
            | none =>
              match addrStr.toNat? with
              | some n => pure (UInt64.ofNat n)
              | none => throw (IO.userError s!"Bad address for {name}: {addrStr}")
          let blocks ← match funcJson.getObjValAs? (α := Array String) "blocks" with
            | .ok bs => pure bs.toList
            | .error e => throw (IO.userError s!"Missing blocks for {name}: {e}")
          specs := specs.push ⟨name, addr, blocks⟩
        return (specs, regions)
      | _ => throw (IO.userError s!"'functions' value is not an object")

/-- Result of function discovery: specs + count of orphan blocks not in any symbol. -/
structure DiscoveryResult where
  functions : Array FunctionSpec
  orphanCount : Nat
  deriving Inhabited

def discoverFunctions (blocks : Array String) (symbols : Array (String × UInt64 × UInt64)) :
    Except String DiscoveryResult := do
  -- Extract entry address from each block
  let mut blockAddrs : Array (UInt64 × String) := #[]
  for blockStr in blocks do
    let addr ← extractIMarkIP blockStr
    blockAddrs := blockAddrs.push (addr, blockStr)
  -- Sort symbols by address for deterministic output
  let sortedSyms := symbols.qsort fun (_, a1, _) (_, a2, _) => a1 < a2
  -- Assign blocks to symbols
  let mut result : Array FunctionSpec := #[]
  let mut assignedCount : Nat := 0
  for (name, addr, size) in sortedSyms do
    let funcBlocks := blockAddrs.filter fun (blockAddr, _) =>
      blockAddr >= addr && blockAddr < addr + size
    -- Sort blocks by address within each function
    let sortedBlocks := funcBlocks.qsort fun (a1, _) (a2, _) => a1 < a2
    let blockStrs := sortedBlocks.map (·.2) |>.toList
    if !blockStrs.isEmpty then
      result := result.push ⟨name, addr, blockStrs⟩
      assignedCount := assignedCount + sortedBlocks.size
  let orphanCount := blockAddrs.size - assignedCount
  return ⟨result, orphanCount⟩

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
    (smtCache : IO.Ref SMTCache)
    (initialFrontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[])
    (addrClassify : Option (AddrClassifier Reg) := none) :
    IO (Option (Nat × Array (Branch (SymSub Reg) (SymPC Reg)))) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  let (rawClosure, ripCount, dataCount) := extractClosure ip_reg bodyArr (dataOnly := true)
  -- Simplify closure PCs with same region classifier used for lifted PCs,
  -- so both sides of the closedness comparison are in the same normal form.
  let closure := match addrClassify with
    | some clf => rawClosure.map (simplifyLoadStorePCR clf)
    | none => rawClosure
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  current := current.insert initBranch
  -- initialFrontier seeded into current AFTER closedness check (needs projection)
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
  -- Convergence via PC signature: syntactic fast-path + SMT semantic check.
  -- convRep{PCs,SynSigs,SemSigs}: one entry per discovered equivalence class.
  -- SynSig = which closure PCs the branch syntactically implies (List Bool).
  -- SemSig = which closure PCs the branch semantically implies (Array Bool);
  --          computed lazily via CVC5 the first time a syntactic mismatch occurs.
  let mut convRepPCs     : Array (SymPC Reg)          := #[initBranch.pc]
  let mut convRepSynSigs : Array (List Bool)           := #[computePCSignature closure initBranch.pc]
  let mut convRepSemSigs : Array (Option (Array Bool)) := #[none]
  -- Build initial frontier: skip + structurally-unique simplified seeds.
  let mut frontierSet : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {initBranch}
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[initBranch]
  for b in initialFrontier do
    match simplifyBranchFull b addrClassify with
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
    let (composedTagged, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr frontier
    -- Strip body indices (not used in this function)
    let composed := composedTagged.map (·.1)
    -- Simplify: load-after-store + constant folding + zero non-projected
    let mut simplified : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut droppedSimplify : Nat := 0
    for b in composed do
      match simplifyBranchFull b addrClassify with
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
    -- Phase 2: PC-signature convergence (syntactic fast-path + SMT semantic).
    -- For each candidate, compute its signature: which closure PCs does it imply?
    -- Fast path: syntactic sig matches an existing rep sig → collapse.
    -- Slow path (CVC5): for candidates with new syntactic sigs, compute semantic sig
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
      -- Collect SMT candidates: those with no syntactic match
      let mut smtCandIdxs : Array Nat := #[]
      for ci in [:semCands.size] do
        unless synMatched.contains ci do
          smtCandIdxs := smtCandIdxs.push ci
      -- Semantic path: only if there are unmatched candidates and closure is non-empty
      let mut candSemSigsArr : Array (Option (Array Bool)) := Array.replicate semCands.size none
      let mut totalSMTQueries := 0
      let mut totalSMTCacheHits := 0
      let mut semMatched : Std.HashSet Nat := {}
      if smtCandIdxs.size > 0 && closure.size > 0 then
        let n := closure.size
        -- Build batch of PCs needing semantic sig computation:
        -- (1) reps with uncomputed sem sigs, (2) SMT candidate branch PCs.
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
        for ci in smtCandIdxs do
          for b in semCands.extract ci (ci + 1) do
            batchPCs := batchPCs.push b.pc
          batchIsRep    := batchIsRep.push false
          batchRepIdxs  := batchRepIdxs.push 0  -- dummy
          batchCandIdxs := batchCandIdxs.push ci
        -- Batch CVC5 with caching: for each pc in batchPCs, n queries (one per closure PC).
        let mut convPairs : Array (SymPC Reg × SymPC Reg) := #[]
        for pc in batchPCs do
          for phi in closure do
            convPairs := convPairs.push (pc, phi)
        let (allSemResults, convHits) ← smtCheckImplCached smtCache convPairs ".lake/smt_semsig.smt2"
        totalSMTQueries := convPairs.size
        totalSMTCacheHits := convHits
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
        -- Compare each SMT cand's semantic sig against all rep semantic sigs
        for ci in smtCandIdxs do
          if let some candSem := candSemSigsArr[ci]! then
            let mut ri := 0
            let mut matched := false
            while !matched && ri < convRepSemSigs.size do
              if let some repSem := convRepSemSigs[ri]! then
                if candSem == repSem then
                  semMatched := semMatched.insert ci
                  matched := true
              ri := ri + 1
      log s!"    smt conv: {totalSMTQueries}q (hits={totalSMTCacheHits} misses={totalSMTQueries - totalSMTCacheHits}) → syn-collapsed={synMatched.size} sem-collapsed={semMatched.size}"
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
      -- h_contains check: every body branch PC's conjuncts are in the closure.
      -- Note: h_contains is about branchingLoopModel (= original body block
      -- summaries), NOT the composed fixpoint (summaryArr). The body branches'
      -- conjuncts are in the full closure by construction (extractClosure).
      -- Uses full closure (data + rip) since the abstract theory doesn't
      -- distinguish between guard types.
      do
        let (fullClosure, _, _) := extractClosure ip_reg bodyArr (dataOnly := false)
        let (fullPass, _, _, dataMissesF) := checkHContains ip_reg bodyArr fullClosure
        if fullPass then
          log s!"    [h_contains] PASS ({bodyArr.size} body branches, {fullClosure.size} closure PCs)"
        else
          log s!"    [h_contains] FAIL: {dataMissesF} data misses ({bodyArr.size} body branches)"
      -- Closedness check on BODY branches (branchingLoopModel).
      -- This is the check that matters for the certificate: are body branch
      -- substitutions closed over the full closure?
      do
        let (fullClosure2, _, _) := extractClosure ip_reg bodyArr (dataOnly := false)
        let mut bodyTrivClosed : Nat := 0
        let mut bodyNeedsSMT : Nat := 0
        let mut bodyViolations : Nat := 0
        let bodyTotal := bodyArr.size * fullClosure2.size
        for b in bodyArr do
          for phi in fullClosure2 do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => bodyTrivClosed := bodyTrivClosed + 1
            | some .true => bodyTrivClosed := bodyTrivClosed + 1
            | some pc' =>
              let inClosure := pc' == .true || fullClosure2.any (fun phi_j => phi_j == pc')
              if inClosure then
                bodyTrivClosed := bodyTrivClosed + 1
              else
                bodyNeedsSMT := bodyNeedsSMT + 1
        -- For non-trivial cases, run SMT equivalence check
        if bodyNeedsSMT > 0 then
          let mut smtPairs : Array (SymPC Reg × SymPC Reg) := #[]
          let mut smtLiftedIdx : Array Nat := #[]
          let mut liftedNeedingCheck2 : Array Nat := #[]
          let mut gIdx : Nat := 0
          for b in bodyArr do
            for phi in fullClosure2 do
              let lifted := substSymPC b.sub phi
              let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
              match SymPC.simplifyConst liftedSimplified with
              | none => pure ()
              | some .true => pure ()
              | some pc' =>
                let inClosure := pc' == .true || fullClosure2.any (fun phi_j => phi_j == pc')
                unless inClosure do
                  for phi_j in fullClosure2 do
                    smtPairs := smtPairs.push (pc', phi_j)
                    smtLiftedIdx := smtLiftedIdx.push gIdx
                  liftedNeedingCheck2 := liftedNeedingCheck2.push gIdx
              gIdx := gIdx + 1
          if smtPairs.size > 0 then
            let mut fwdP : Array (SymPC Reg × SymPC Reg) := #[]
            let mut revP : Array (SymPC Reg × SymPC Reg) := #[]
            for (cp, rp) in smtPairs do
              fwdP := fwdP.push (cp, rp)
              revP := revP.push (rp, cp)
            let (fwdR, _) ← smtCheckImplCached smtCache fwdP ".lake/smt_body_closed.smt2"
            let (revR, _) ← smtCheckImplCached smtCache revP ".lake/smt_body_closed.smt2"
            let mut closedBySMT2 : Std.HashSet Nat := {}
            for i in [:smtPairs.size] do
              if h1 : i < fwdR.size then
                if h2 : i < revR.size then
                  if fwdR[i] && revR[i] then
                    closedBySMT2 := closedBySMT2.insert smtLiftedIdx[i]!
            for gIdx2 in liftedNeedingCheck2 do
              unless closedBySMT2.contains gIdx2 do
                bodyViolations := bodyViolations + 1
        let bodyClosed := bodyViolations == 0
        if bodyClosed then
          log s!"    [body-closed] PASS: body branches closed over full closure ({bodyArr.size}×{fullClosure2.size}, trivial={bodyTrivClosed})"
        else
          log s!"    [body-closed] FAIL: {bodyViolations} violations ({bodyArr.size}×{fullClosure2.size}, trivial={bodyTrivClosed}, smt_cands={bodyNeedsSMT})"
      -- Task 1B: Closure closedness verification (on summaryArr, for reference).
      -- For each branch b in summaryArr and each data guard PC phi in closure:
      --   lifted = substSymPC b.sub phi  (the pc_lift from VexSummary/VexCompTree)
      --   simplified = simplifyLoadStorePC lifted |> SymPC.simplifyConst
      --   check: simplified ≡ some phi_j in closure, or trivially true/false
      do
        log s!"    [closedness] checking {summaryArr.size} branches × {closure.size} guards..."
        let mut trivClosedPairs : Nat := 0   -- simplified to true/false or syntactic match
        let mut needsSMTPairs : Nat := 0      -- require SMT semantic check
        -- SMT query data: for each lifted PC that fails syntactic check,
        -- compare against each phi_j in closure
        let mut closedQueryPairs : Array (SymPC Reg × SymPC Reg) := #[]
        let mut closedQueryLiftedIdx : Array Nat := #[]
        let mut liftedNeedingCheck : Array Nat := #[]  -- globalIdx of non-trivial lifted PCs
        let mut globalIdx : Nat := 0
        for b in summaryArr do
          for phi in closure do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
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
                -- Need SMT check: is pc' semantically equiv to some phi_j?
                for phi_j in closure do
                  closedQueryPairs := closedQueryPairs.push (pc', phi_j)
                  closedQueryLiftedIdx := closedQueryLiftedIdx.push globalIdx
                liftedNeedingCheck := liftedNeedingCheck.push globalIdx
                needsSMTPairs := needsSMTPairs + 1
            globalIdx := globalIdx + 1
        log s!"    [closedness] trivial={trivClosedPairs}/{globalIdx} smt_candidates={needsSMTPairs}"
        -- Run SMT semantic equivalence check via cached implication pairs.
        -- Equivalence (A ↔ B) = (A→B) ∧ (B→A): decompose into two implication queries.
        let mut closednessViolations : Nat := 0
        if closedQueryPairs.size > 0 then
          -- Build forward (cp→rp) and reverse (rp→cp) implication pairs
          let mut fwdPairs : Array (SymPC Reg × SymPC Reg) := #[]
          let mut revPairs : Array (SymPC Reg × SymPC Reg) := #[]
          for (cp, rp) in closedQueryPairs do
            fwdPairs := fwdPairs.push (cp, rp)
            revPairs := revPairs.push (rp, cp)
          let (fwdResults, fwdHits) ← smtCheckImplCached smtCache fwdPairs ".lake/smt_closedness.smt2"
          let (revResults, revHits) ← smtCheckImplCached smtCache revPairs ".lake/smt_closedness.smt2"
          -- A pair is equivalent iff both forward AND reverse implications hold
          let mut closedBySMT : Std.HashSet Nat := {}
          for i in [:closedQueryPairs.size] do
            if h1 : i < fwdResults.size then
              if h2 : i < revResults.size then
                if fwdResults[i] && revResults[i] then
                  closedBySMT := closedBySMT.insert closedQueryLiftedIdx[i]!
          -- Violations: lifted PCs not closed by SMT
          for gIdx in liftedNeedingCheck do
            unless closedBySMT.contains gIdx do
              closednessViolations := closednessViolations + 1
          let clTotalQueries := closedQueryPairs.size * 2
          log s!"    [closedness] smt: {clTotalQueries} queries (hits={fwdHits + revHits} misses={clTotalQueries - fwdHits - revHits}), {closedBySMT.size} closed, {closednessViolations} violations"
        let isClosed := closednessViolations == 0
        log s!"    [closedness] closure closed: {if isClosed then "YES" else "NO"}, violations={closednessViolations}"
      -- Diagnostic: dump closure PCs and non-closed lifted PCs for analysis
      do
        log s!"    [closure-diag] {closure.size} closure PCs:"
        let mut ci : Nat := 0
        for pc in closure do
          log s!"      φ[{ci}]: {SymPC.toSMTLib pc}  (loads={SymPC.hasLoad pc})"
          ci := ci + 1
        -- Dump first few non-closed lifted PCs
        let mut dumpCount : Nat := 0
        let mut b_idx : Nat := 0
        for b in summaryArr do
          let mut phi_idx : Nat := 0
          for phi in closure do
            if dumpCount < 10 then
              let lifted := substSymPC b.sub phi
              let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
              match SymPC.simplifyConst liftedSimplified with
              | none => pure ()  -- trivial false
              | some .true => pure ()  -- trivial true
              | some pc' =>
                -- Check if it matches any closure member
                let mut matched := false
                for phi_j in closure do
                  if phi_j == pc' then matched := true
                unless matched do
                  log s!"      NONCLOSED b[{b_idx}]×φ[{phi_idx}]: {SymPC.toSMTLib pc'}"
                  log s!"        original guard: {SymPC.toSMTLib phi}"
                  log s!"        loads={SymPC.hasLoad pc'}"
                  dumpCount := dumpCount + 1
            phi_idx := phi_idx + 1
          b_idx := b_idx + 1
        log s!"    [closure-diag] showed {dumpCount} non-closed lifted PCs (first 10)"
      -- Phase 2: Template basis SemClosed experiment.
      -- Anti-unify non-closed lifted PCs with originals to discover template structure,
      -- then check if one round of basis expansion makes SemClosed pass.
      do
        -- Step 1: Collect all non-closed lifted PCs with their originals
        let mut nonClosedLifted : Array (SymPC Reg) := #[]
        let mut nonClosedOriginals : Array (SymPC Reg) := #[]
        for b in summaryArr do
          for phi in closure do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => pure ()  -- trivial false
            | some .true => pure ()  -- trivial true
            | some pc' =>
              let inClosure := pc' == .true || closure.any (fun phi_j => phi_j == pc')
              unless inClosure do
                nonClosedLifted := nonClosedLifted.push pc'
                nonClosedOriginals := nonClosedOriginals.push phi
        log s!"    [template-exp] {nonClosedLifted.size} non-closed lifted PCs from {summaryArr.size}×{closure.size} pairs"
        -- Step 2: Anti-unify each (original, lifted) pair to discover template structure
        if nonClosedLifted.size > 0 then
          let mut totalHoles : Nat := 0
          let mut maxHoles : Nat := 0
          let paired := nonClosedOriginals.zip nonClosedLifted
          for (orig, lifted) in paired do
            let (template, _subs) := antiUnify orig lifted
            let holes := template.holeCount
            totalHoles := totalHoles + holes
            if holes > maxHoles then maxHoles := holes
          log s!"    [template-exp] anti-unification: avg_holes={totalHoles / nonClosedLifted.size} max_holes={maxHoles}"
          -- Step 3: Build expanded basis = closure ∪ non-closed lifted PCs (deduped)
          let mut expandedBasis : Array (SymPC Reg) := closure
          let mut seen : Std.HashSet (SymPC Reg) :=
            closure.foldl (fun s pc => s.insert pc) {}
          for pc in nonClosedLifted do
            unless seen.contains pc do
              seen := seen.insert pc
              expandedBasis := expandedBasis.push pc
          log s!"    [template-exp] expanded basis: {expandedBasis.size} PCs (was {closure.size})"
          -- Step 4: Re-check SemClosed against expanded basis.
          -- For each branch b and each φ in expanded basis, is substSymPC b.sub φ
          -- determined by the expanded basis? (Two-state CVC5 query)
          let mut expandedLiftedPCs : Array (SymPC Reg) := #[]
          let mut expandedTrivial : Nat := 0
          for b in summaryArr do
            for phi in expandedBasis do
              let lifted := substSymPC b.sub phi
              let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
              match SymPC.simplifyConst liftedSimplified with
              | none => expandedTrivial := expandedTrivial + 1
              | some .true => expandedTrivial := expandedTrivial + 1
              | some pc' =>
                let inBasis := expandedBasis.any (fun phi_j => phi_j == pc')
                if inBasis then
                  expandedTrivial := expandedTrivial + 1
                else
                  expandedLiftedPCs := expandedLiftedPCs.push pc'
          let totalPairs := summaryArr.size * expandedBasis.size
          log s!"    [template-exp] expanded SemClosed: trivial={expandedTrivial}/{totalPairs} smt_candidates={expandedLiftedPCs.size}"
          if expandedLiftedPCs.size > 0 then
            let results ← smtCheckSemClosedBatch expandedLiftedPCs expandedBasis log
            let violations := results.filter (· == false) |>.size
            log s!"    [template-exp] RESULT: {violations} violations out of {expandedLiftedPCs.size} SMT checks"
            if violations == 0 then
              log s!"    [template-exp] *** ONE-ROUND EXPANSION SUFFICES — template basis gives SemClosed ***"
            else
              log s!"    [template-exp] *** Template basis INSUFFICIENT — need approach D (memory regions) ***"
          else
            log s!"    [template-exp] *** ALL TRIVIALLY CLOSED — template basis gives SemClosed ***"
      -- Atom-closure check (approach B): does the expanded basis satisfy
      -- h_atoms_closed from semClosed_of_liftedAtomsInBasis?
      -- If yes: SemClosed holds by structural theorem, no SMT needed.
      do
        -- Build expanded basis for body branches (branchingLoopModel)
        let (fullClosure3, _, _) := extractClosure ip_reg bodyArr (dataOnly := false)
        -- One-round expansion on body branches
        let mut atomBasis : Array (SymPC Reg) := fullClosure3
        let mut atomSeen : Std.HashSet (SymPC Reg) :=
          fullClosure3.foldl (fun s pc => s.insert pc) {}
        -- Add full branch PCs for h_contains
        for b in bodyArr do
          unless atomSeen.contains b.pc do
            atomSeen := atomSeen.insert b.pc
            atomBasis := atomBasis.push b.pc
        -- Add non-closed lifted PCs (one round)
        for b in bodyArr do
          for phi in fullClosure3 do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => pure ()
            | some .true => pure ()
            | some pc' =>
              unless atomSeen.contains pc' do
                atomSeen := atomSeen.insert pc'
                atomBasis := atomBasis.push pc'
        -- Now check: for each body branch and expanded basis PC,
        -- are all atoms of the lifted PC in the expanded basis?
        let mut atomViolations : Nat := 0
        let mut atomTotal : Nat := 0
        let atomBasisSet : Std.HashSet (SymPC Reg) :=
          atomBasis.foldl (fun s pc => s.insert pc) {}
        for b in bodyArr do
          for phi in atomBasis do
            atomTotal := atomTotal + 1
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => pure ()  -- trivial false, atoms vacuously in basis
            | some .true => pure ()  -- trivial true, no atoms
            | some pc' =>
              for a in SymPC.atoms pc' do
                unless atomBasisSet.contains a do
                  atomViolations := atomViolations + 1
        if atomViolations == 0 then
          log s!"    [atom-closed] PASS: expanded basis is atom-closed ({atomBasis.size} PCs, {atomTotal} pairs checked)"
          log s!"    [atom-closed] *** semClosed_of_liftedAtomsInBasis applies — SemClosed by structural theorem ***"
        else
          log s!"    [atom-closed] FAIL: {atomViolations} atom violations ({atomBasis.size} PCs, {atomTotal} pairs)"
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
    (regions : Array MemRegion := #[])
    (log : String → IO Unit) :
    IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  -- Build address classifier from ELF memory regions.
  -- rsp and rbp are stack registers — addresses relative to them are in the
  -- stack region, which doesn't overlap any loaded ELF section.
  let addrClassify : Option (AddrClassifier Amd64Reg) :=
    if regions.size > 0 then
      some (classifyAddr regions [Amd64Reg.rsp, Amd64Reg.rbp])
    else none
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
      log s!"  {func.name} @ 0x{String.ofList (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches"
  -- Phase 1: Compute leaf function (next_sym) fixpoint — no summaries needed
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  -- Green-style SMT query cache: shared across all function stabilizations
  let smtCache ← IO.mkRef ({} : SMTCache)
  log s!"\n--- Phase 1: Leaf function (next_sym) ---"
  let t0 ← IO.monoMsNow
  let (nextSymName, nextSymBody) := funcBlocks[0]!
  -- Use computeFunctionStabilization directly (returns branch array as summary).
  -- Don't double-run with computeStabilizationHS — that keeps two copies of deeply-nested
  -- symbolic branches alive simultaneously, causing OOM.
  match ← computeFunctionStabilization ip_reg nextSymBody {} 200 log smtCache (addrClassify := addrClassify) with
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
      match ← computeFunctionStabilization ip_reg nonCallBody {} 30 log smtCache (initialFrontier := callResults) (addrClassify := addrClassify) with
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
  -- SMT cache summary
  let cacheContents ← smtCache.get
  log s!"\n=== SMT Cache Summary ==="
  log s!"  cache entries: {cacheContents.size}"
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
def ppExpr : SymExpr Amd64Reg → String
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
  | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => s!"({ppExpr a}>>{ppExpr b})"
  | .shl64 a b => s!"({ppExpr a}<<{ppExpr b})"
  | .low32 e   => s!"lo32({ppExpr e})"
  | .uext32 e  => s!"zx32({ppExpr e})"
  | .sext32to64 e => s!"sx32({ppExpr e})"
  | _ => "..."

/-- Pretty-print a SymPC atom as a character condition on rax. -/
def ppCharCond (rax : Amd64Reg) : SymPC Amd64Reg → String
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
  s!"0x{String.ofList (Nat.toDigits 16 a.toNat)}"

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
def exprUsesRSP : SymExpr Amd64Reg → Bool
  | .reg .rsp => true
  | .add64 a b | .sub64 a b => exprUsesRSP a || exprUsesRSP b
  | .load _ _ addr => exprUsesRSP addr
  | _ => false

/-- Extract the constant return address pushed by a call instruction at [rsp - k]. -/
def extractCallReturn (mem : SymMem Amd64Reg) : Option UInt64 :=
  match mem with
  | .base => none
  | .store _ inner addr (.const v) =>
    if exprUsesRSP addr then some v else extractCallReturn inner
  | .store _ inner _ _ => extractCallReturn inner

/-- Strip sign-extension / low-extract wrappers and +offset to reach a raw constant.
    Used to decode the character constants inside VEX-style signed-comparison expressions
    (e.g. sx32(lo32(lo32(const '/')))+2^63  →  '/').
    Returns Some v only if v is a printable ASCII char (32..126). -/
def stripToCharConst : SymExpr Amd64Reg → Option UInt64
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
def dfsExtractProds
    (cur : UInt64)
    (steps : Array String)
    (cfg : AnnotatedCFG)
    (blocks : Std.HashSet UInt64)
    (funcEntries : Std.HashMap UInt64 String)
    (visited : Std.HashSet UInt64)
    (fuel : Nat := 61) :
    Array (Array String) :=
  match fuel with
  | 0 => #[steps]
  | fuel' + 1 => if visited.contains cur then #[steps] else Id.run do
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
            (dfsExtractProds ret steps' cfg blocks funcEntries visited' fuel')
        else
          allPaths := allPaths.push steps'  -- call is at function tail
      | none =>
        allPaths := allPaths.push steps'  -- can't determine continuation
    | none =>
      -- Internal transition, known-unknown helper, or function exit
      if blocks.contains tgt then
        -- Internal transition within this function: recurse without recording a step
        allPaths := allPaths.append
          (dfsExtractProds tgt steps cfg blocks funcEntries visited' fuel')
      else
        -- External call to unknown helper (e.g. a helper like isdigit called before next_sym).
        -- Follow the return address to find the continuation (the helper is transparent).
        match retOpt with
        | some ret =>
          if blocks.contains ret then
            allPaths := allPaths.append
              (dfsExtractProds ret steps cfg blocks funcEntries visited' fuel')
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
    |>.insert "sum"        [["term"], ["sum", "'+'", "term"], ["sum", "'-'", "term"]]
    |>.insert "test"       [["sum"], ["sum", "'<'", "sum"]]
    |>.insert "expr"       [["test"], ["id", "'='", "expr"]]
    |>.insert "paren_expr" [["'('", "expr", "')'"]]
    |>.insert "statement"  [
        ["'if'", "paren_expr", "statement"],
        ["'if'", "paren_expr", "statement", "'else'", "statement"],
        ["'while'", "paren_expr", "statement"],
        ["'do'", "statement", "'while'", "paren_expr", "';'"],
        ["'{'", "statements", "'}'"],
        ["expr", "';'"],
        ["';'"]
      ]
    |>.insert "statements" [["statement"], ["statement", "statements"]]

/-- BFS to find all blocks reachable from entry, following:
    - internal transitions (tgt in blocks)
    - return continuations after external calls (retOpt if tgt not in blocks) -/
def cfgReachable (entry : UInt64) (cfg : AnnotatedCFG) (blocks : Std.HashSet UInt64)
    (_funcEntries : Std.HashMap UInt64 String) :
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
  let rawPaths := dfsExtractProds entryAddr #[] cfg blocks funcEntries {}
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
                (dfsExtractProds ret #[callee] cfg blocks funcEntries {})
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

/-! ## LTS Extraction from Converged Branches

The converged branch set IS the LTS implicitly — each branch encodes one
transition: src = rip guard address, tgt = rip target, label = decoded data
guard as a CharClass. Making it explicit enables DFA/EBNF specialization. -/

/-- A character/token class decoded from a data guard PC — regex style. -/
inductive CharClass where
  | literal : Char → CharClass          -- exact printable character match
  | tokenCode : UInt64 → CharClass      -- token type code (non-printable constant)
  | range : Char → Char → CharClass     -- inclusive character range [lo..hi]
  | negated : CharClass → CharClass     -- complement
  | conj : CharClass → CharClass → CharClass  -- intersection
  | any : CharClass                     -- any byte / epsilon
  | empty : CharClass                   -- contradictory / impossible guard
  deriving BEq, Hashable, Inhabited

/-- Render a CharClass as a regex-style string. -/
def CharClass.toString : CharClass → String
  | .literal c => s!"'{c}'"
  | .tokenCode n => s!"tok{n.toNat}"
  | .range lo hi => s!"[{lo}-{hi}]"
  | .negated (.literal c) => s!"[^{c}]"
  | .negated cc => s!"[^{cc.toString}]"
  | .conj a b => s!"{a.toString}&{b.toString}"
  | .any => "."
  | .empty => "∅"

instance : ToString CharClass := ⟨CharClass.toString⟩

/-- Extract a small constant from a wrapped SymExpr (strips sext, zext, low32, add64).
    Unlike stripToCharConst, accepts ALL constants < 256, not just printable. -/
def stripToSmallConst : SymExpr Amd64Reg → Option UInt64
  | .const v => if v.toNat < 256 then some v else none
  | .low32 inner | .uext32 inner | .sext8to32 inner | .sext32to64 inner =>
    stripToSmallConst inner
  | .add64 a b => stripToSmallConst a <|> stripToSmallConst b
  | _ => none

/-- Check if a SymExpr loads via register-relative addresses, indicating a local
    variable rather than the global `sym` variable. The global `sym` is accessed
    through a chain of loads from constant addresses (e.g., load(mem, load(mem, 0x500030))).
    Local variables use register-relative addresses (e.g., load(mem, rbp-16)). -/
def exprLoadsViaRegAddr : SymExpr Amd64Reg → Bool
  | .load _ _ addr => addrUsesRegs addr
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e | .not64 e | .not32 e => exprLoadsViaRegAddr e
  | .add64 a b | .sub64 a b | .xor64 a b | .and64 a b | .or64 a b
  | .sub32 a b | .shl32 a b | .and32 a b | .or32 a b | .xor32 a b | .shl64 a b | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => exprLoadsViaRegAddr a || exprLoadsViaRegAddr b
  | _ => false
where
  /-- Check if an address expression uses registers (for load address chains). -/
  addrUsesRegs : SymExpr Amd64Reg → Bool
  | .reg _ => true
  | .const _ => false
  | .load _ _ innerAddr => addrUsesRegs innerAddr  -- chained load: check inner address
  | .add64 a b | .sub64 a b | .xor64 a b | .and64 a b | .or64 a b
  | .sub32 a b | .shl32 a b | .and32 a b | .or32 a b | .xor32 a b | .shl64 a b | .shr64 a b | .mul64 a b | .mul32 a b | .sar64 a b | .sar32 a b => addrUsesRegs a || addrUsesRegs b
  | .low32 e | .uext32 e | .sext8to32 e | .sext32to64 e | .not64 e | .not32 e => addrUsesRegs e

/-- Extract a constant (printable char or token code) from a SymExpr. -/
def extractConstFromExpr (e : SymExpr Amd64Reg) : Option (CharClass) :=
  match stripToSmallConst e with
  | some v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then some (.literal (Char.ofNat n))
    else some (.tokenCode v)
  | none => none

/-- Decode a single SymPC atom into a CharClass component.
    Uses extractConstFromExpr to handle VEX-style wrapped expressions
    and both printable characters AND non-printable token type codes. -/
private def decodeAtom (pc : SymPC Amd64Reg) : Option CharClass :=
  match pc with
  | .eq l r =>
    -- Extract constants from both sides, but skip when the other side loads via
    -- register-relative address, indicating a local variable comparison, not a sym check.
    let cl := if exprLoadsViaRegAddr r then none else extractConstFromExpr l
    let cr := if exprLoadsViaRegAddr l then none else extractConstFromExpr r
    match cl <|> cr with
    | some cc => some cc
    | none => none
  | .le l r =>
    -- For range bounds, we still need character values
    let lChar := extractCharConstFromExpr l
    let rChar := extractCharConstFromExpr r
    match lChar, rChar with
    | some lo, none => some (.range lo (Char.ofNat 127))
    | none, some hi => some (.range (Char.ofNat 0) hi)
    | _, _ => none
  | .lt l r =>
    let lChar := extractCharConstFromExpr l
    let rChar := extractCharConstFromExpr r
    match lChar, rChar with
    | some lo, none =>
      some (.range (Char.ofNat (lo.toNat + 1)) (Char.ofNat 127))
    | none, some hi =>
      if hi.toNat > 0 then some (.range (Char.ofNat 0) (Char.ofNat (hi.toNat - 1)))
      else none
    | _, _ => none
  | .not inner =>
    match decodeAtom inner with
    | some cc => some (.negated cc)
    | none => none
  | _ => none

/-- Decode a full data guard PC into a CharClass.
    Collects decoded atoms, intersects ranges to produce compact classes. -/
def decodeCharClass (pc : SymPC Amd64Reg) : CharClass :=
  let atoms := SymPC.conjuncts pc
  let decoded := atoms.filterMap decodeAtom
  match decoded with
  | [] => .any
  | [c] => c
  | c :: rest => rest.foldl .conj c

/-- Simplify a pair of CharClass values under conjunction.
    Returns none if the pair doesn't match any special rule. -/
private def CharClass.simplifyPair (a b : CharClass) : Option CharClass :=
  match a, b with
  -- empty propagation
  | .empty, _ | _, .empty => some .empty
  -- any is identity for conj
  | .any, x | x, .any => some x
  -- range ∩ range → narrower range
  | .range lo1 hi1, .range lo2 hi2 =>
    let lo := if lo1 > lo2 then lo1 else lo2
    let hi := if hi1 < hi2 then hi1 else hi2
    if lo == hi then some (.literal lo)
    else if lo < hi then some (.range lo hi)
    else some .empty
  -- literal ∩ range
  | .literal c, .range lo hi | .range lo hi, .literal c =>
    if c >= lo && c <= hi then some (.literal c) else some .empty
  -- tokenCode ∩ tokenCode
  | .tokenCode a, .tokenCode b =>
    if a == b then some (.tokenCode a) else some .empty
  -- tokenCode ∩ negated(tokenCode)
  | .tokenCode a, .negated (.tokenCode b) | .negated (.tokenCode b), .tokenCode a =>
    if a == b then some .empty else some (.tokenCode a)
  -- literal ∩ negated(literal)
  | .literal a, .negated (.literal b) | .negated (.literal b), .literal a =>
    if a == b then some .empty else some (.literal a)
  -- literal ∩ literal
  | .literal a, .literal b =>
    if a == b then some (.literal a) else some .empty
  | _, _ => none

/-- Flatten a conjunction tree into a list of conjuncts. -/
def CharClass.flattenConj : CharClass → List CharClass
  | .conj a b => a.flattenConj ++ b.flattenConj
  | other => [other]

/-- Simplify a flat list of conjuncts: if there is exactly one positive tokenCode
    and all other conjuncts are negated tokenCodes with different values, simplify
    to just the positive tokenCode. Also handles positive literal + negated tokenCodes. -/
def CharClass.simplifyFlat (parts : List CharClass) : Option CharClass :=
  let positives := parts.filter fun
    | .tokenCode _ | .literal _ | .range _ _ => true
    | _ => false
  let negatives := parts.filter fun
    | .negated _ => true
    | _ => false
  -- If exactly one positive and the rest are negatives, check consistency
  if positives.length == 1 && positives.length + negatives.length == parts.length then
    let pos := positives.head!
    let allConsistent := negatives.all fun
      | .negated (.tokenCode b) =>
        match pos with
        | .tokenCode a => a != b  -- negating a different code is consistent
        | .literal _ | .range _ _ => true  -- negating tokenCode is consistent with literal/range
        | _ => false
      | .negated (.literal b) =>
        match pos with
        | .literal a => a != b
        | .tokenCode _ | .range _ _ => true
        | _ => false
      | _ => false
    if allConsistent then some pos else none
  else none

/-- Simplify a CharClass by intersecting ranges and resolving conjunctions. -/
def CharClass.simplify : CharClass → CharClass
  | .conj a b =>
    let a' := a.simplify
    let b' := b.simplify
    match CharClass.simplifyPair a' b' with
    | some result => result
    | none =>
      -- Try flatten-and-simplify for multi-level conjunctions
      let flat := CharClass.flattenConj (.conj a' b')
      match CharClass.simplifyFlat flat with
      | some result => result
      | none => .conj a' b'
  | .negated inner => match inner.simplify with
    | .empty => .any  -- negation of empty = everything (but shouldn't arise)
    | inner' => .negated inner'
  | other => other

/-- Token name table: maps token type codes to human-readable names.
    Built from converged next_sym summary (rax at return → token name). -/
abbrev TokenNameTable := Std.HashMap UInt64 String

/-- Infer a token class name from a CharClass, using optional token name table. -/
def charClassToTokenName (tokenNames : TokenNameTable := {}) : CharClass → String
  | .literal c => s!"'{c}'"
  | .tokenCode n =>
    match tokenNames.get? n with
    | some name => name
    | none => s!"tok{n.toNat}"
  | .range lo hi => s!"[{lo}-{hi}]"
  | .negated cc => s!"[^{cc}]"
  | .any => "token"
  | .empty => "∅"
  | cc => cc.toString

/-- A single LTS transition: source state, label, target state. -/
structure LTSTransition where
  src : UInt64
  label : CharClass
  tgt : UInt64
  deriving BEq, Hashable

/-- An extracted LTS: states are block addresses, labels are CharClasses. -/
structure ExtractedLTS where
  transitions : Array LTSTransition
  states : Std.HashSet UInt64
  deriving Inhabited

/-- Find the largest block entry address that is ≤ the given address.
    Redirects mid-block jump targets to the containing block's entry. -/
def redirectToBlockEntry (addr : UInt64) (sortedEntries : Array UInt64) : UInt64 := Id.run do
  let mut best := addr
  for entry in sortedEntries do
    if entry <= addr then best := entry
  return best

/-- Extract an LTS from an array of converged branches.
    Each branch yields: src = rip guard, tgt = rip target, label = data guard decoded.
    Mid-block jump targets are redirected to the containing block's entry address. -/
def extractLTS (ip_reg : Amd64Reg)
    (branches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String := {}) :
    ExtractedLTS :=
  -- First pass: collect block entry addresses (sources)
  let blockEntries := Id.run do
    let mut entries : Std.HashSet UInt64 := {}
    for b in branches do
      match extractRipGuard ip_reg b.pc with
      | some src => entries := entries.insert src
      | none => pure ()
    return entries.toArray.qsort (· < ·)
  let blockSet : Std.HashSet UInt64 := blockEntries.foldl (fun s e => s.insert e) {}
  -- Second pass: extract transitions, redirecting mid-block targets
  let trans := Id.run do
    let mut trans : Array LTSTransition := #[]
    for b in branches do
      match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
      | some src, some tgt =>
        let dataGuard := stripRipGuards ip_reg b.pc
        let label := (decodeCharClass dataGuard).simplify
        -- Redirect mid-block targets to containing block entry
        let tgt' := if blockSet.contains tgt || funcEntries.contains tgt then tgt
                    else redirectToBlockEntry tgt blockEntries
        trans := trans.push ⟨src, label, tgt'⟩
      | _, _ => pure ()
    return trans
  let states := trans.foldl (fun s t => (s.insert t.src).insert t.tgt) ({} : Std.HashSet UInt64)
  { transitions := trans, states := states }

/-- Print an LTS transition table. -/
def printLTS (log : String → IO Unit) (name : String) (lts : ExtractedLTS) : IO Unit := do
  log s!"\n=== LTS: {name} ({lts.transitions.size} transitions, {lts.states.size} states) ==="
  -- Group by source
  let mut bySource : Std.HashMap UInt64 (Array LTSTransition) := {}
  for t in lts.transitions do
    let arr := bySource.getD t.src #[]
    bySource := bySource.insert t.src (arr.push t)
  for (src, edges) in bySource.toArray do
    log s!"  {hexAddr src}:"
    for t in edges do
      log s!"    --[{t.label}]--> {hexAddr t.tgt}"

/-! ## DFA Specialization for Tokenizer -/

/-- A DFA state: block address, whether it's accepting, and if so the token type. -/
structure DFAState where
  addr : UInt64
  isAccept : Bool
  tokenType : Option String  -- rax value at return → token class
  deriving Inhabited

/-- Extract the rax value from a branch's substitution for token type identification. -/
def extractRaxValue (sub : SymSub Amd64Reg) : Option String :=
  match sub.regs .rax with
  | .const v =>
    let n := v.toNat
    if n ≥ 32 && n ≤ 126 then some s!"'{Char.ofNat n}'"
    else some s!"{n}"
  | _ => none

/-- Print DFA for next_sym: transitions, accept states with token types. -/
def printTokenizerDFA (log : String → IO Unit)
    (lts : ExtractedLTS)
    (funcBlocks : Std.HashSet UInt64)
    (bodyBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (entryAddr : UInt64) : IO Unit := do
  log s!"\n=== Tokenizer DFA (next_sym) ==="
  log s!"  entry: {hexAddr entryAddr}"
  -- Accept states: transitions whose target is outside the function's block set
  let mut acceptTokens : Std.HashMap UInt64 String := {}  -- src → token type
  for b in bodyBranches do
    match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
    | some src, some tgt =>
      if !funcBlocks.contains tgt then
        -- This is a return transition; extract rax as token type
        let tok := match extractRaxValue b.sub with
          | some v => v
          | none => "?"
        acceptTokens := acceptTokens.insert src tok
    | _, _ => pure ()
  log s!"  accept states: {acceptTokens.size}"
  for (addr, tok) in acceptTokens.toArray do
    log s!"    {hexAddr addr} → token={tok}"
  -- Print transitions (only internal ones within next_sym)
  let mut bySource : Std.HashMap UInt64 (Array LTSTransition) := {}
  let mut internalCount := 0
  for t in lts.transitions do
    if funcBlocks.contains t.src && funcBlocks.contains t.tgt then
      let arr := bySource.getD t.src #[]
      bySource := bySource.insert t.src (arr.push t)
      internalCount := internalCount + 1
  log s!"  internal transitions: {internalCount}"
  for (src, edges) in bySource.toArray do
    let acceptMark := if acceptTokens.contains src then s!" [accept→{acceptTokens.get! src}]" else ""
    log s!"  {hexAddr src}{acceptMark}:"
    for t in edges do
      log s!"    --[{t.label}]--> {hexAddr t.tgt}"

/-! ## Parser Detection — Conservative Constructive Evidence

Given converged function summaries from stratified fixpoint, detect whether
the binary is a parser and construct a ParserStructure with:
- Which function is the lexer (token producer)
- Which functions are nonterminals (token consumers)
- Derived token names from lexer branch guards

Detection uses IsTokenConfig (World 1, rax proxy): the lexer is the unique
function that produces diverse rax constants, called by ≥2 consumer functions. -/

/-- How the binary classifies an LTS transition. -/
inductive TransitionRole where
  | terminal : TransitionRole              -- consumes a token
  | nonterminal : String → TransitionRole  -- invokes another classifier
  | internal : TransitionRole              -- function-internal (not grammar-relevant)

/-- Evidence that a binary classifies regions of a token stream.
    Construction-method-agnostic: IsTokenConfig, World 2 detection, or
    manual annotation all produce the same structure. -/
structure ParserStructure where
  /-- The region classifiers (nonterminals) -/
  classifiers : Array FunctionSpec
  /-- The lexer function name -/
  lexerName : String
  /-- The lexer function entry address -/
  lexerAddr : UInt64
  /-- Which classifier is the entry point (start symbol) -/
  entryClassifier : UInt64
  /-- Token name table for rendering -/
  tokenNames : TokenNameTable

/-- Evidence for IsTokenConfig conditions (Bool witnesses). -/
structure TokenConfigEvidence where
  lexer : FunctionSpec
  raxValues : Array UInt64
  consumers : Array FunctionSpec
  callEdges : Array (UInt64 × UInt64)
  deriving Inhabited

/-- Extract the raw rax UInt64 from a branch substitution (for producer detection). -/
def extractRaxValueRaw (sub : SymSub Amd64Reg) : Option UInt64 :=
  match sub.regs .rax with
  | .const v => some v
  | _ => none

/-- Resolve a SymExpr to a constant, substituting known rip value.
    Handles patterns like add64(reg(rip), const(offset)), const(v), etc. -/
def resolveExprConst (ripVal : Option UInt64) : SymExpr Amd64Reg → Option UInt64
  | .const v => some v
  | .reg .rip => ripVal
  | .add64 a b => do
    let va ← resolveExprConst ripVal a
    let vb ← resolveExprConst ripVal b
    return va + vb
  | .sub64 a b => do
    let va ← resolveExprConst ripVal a
    let vb ← resolveExprConst ripVal b
    return va - vb
  | .low32 inner => do
    let v ← resolveExprConst ripVal inner
    return v &&& 0xFFFFFFFF
  | .sext32to64 inner => resolveExprConst ripVal inner
  | .uext32 inner => resolveExprConst ripVal inner
  | _ => none

/-- Extract (address, value) pairs from constant stores in a memory chain.
    Resolves RIP-relative addresses using the known rip value from the branch's PC guard.
    Returns array of (store_addr, stored_value). -/
def extractConstStores (ripVal : Option UInt64) : SymMem Amd64Reg → Array (UInt64 × UInt64)
  | .base => #[]
  | .store _w inner addr val =>
    let rest := extractConstStores ripVal inner
    match resolveExprConst ripVal addr, resolveExprConst ripVal val with
    | some a, some v => rest.push (a, v)
    | _, _ => rest

/-- Build call graph by scanning raw body branches for rip targets matching function entries.
    Returns array of (caller_addr, callee_addr) edges. -/
def buildCallGraph
    (functions : Array FunctionSpec)
    (log : String → IO Unit) :
    IO (Array (UInt64 × UInt64)) := do
  let ip_reg := Amd64Reg.rip
  let mut funcEntrySet : Std.HashSet UInt64 := {}
  for f in functions do
    funcEntrySet := funcEntrySet.insert f.entryAddr
  let mut edges : Array (UInt64 × UInt64) := #[]
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error _ => pure ()
    | .ok pairs =>
      let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
      for b in bodyArr do
        match extractRipTarget ip_reg b.sub with
        | some tgt =>
          if funcEntrySet.contains tgt && tgt != func.entryAddr then
            let edgeExists := edges.any fun (s, t) => s == func.entryAddr && t == tgt
            if !edgeExists then
              edges := edges.push (func.entryAddr, tgt)
        | none => pure ()
  log s!"\n=== Parser Detection: Call Graph ({edges.size} edges) ==="
  for (src, tgt) in edges do
    let srcName := functions.findSome? fun f => if f.entryAddr == src then some f.name else none
    let tgtName := functions.findSome? fun f => if f.entryAddr == tgt then some f.name else none
    log s!"  {srcName.getD (hexAddr src)} → {tgtName.getD (hexAddr tgt)}"
  return edges

/-- Find producer functions: those that write ≥2 distinct constant values to the SAME
    memory address on return transitions. This detects the token variable (e.g., `sym`)
    without requiring rax to carry the return value.
    Returns array of (function addr, distinct token values, token variable address). -/
def findProducers
    (functions : Array FunctionSpec)
    (_summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (log : String → IO Unit) :
    IO (Array (UInt64 × Array UInt64)) := do
  let ip_reg := Amd64Reg.rip
  let mut producers : Array (UInt64 × Array UInt64) := #[]
  log s!"\n--- Producer Identification ---"
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error _ =>
      log s!"  {func.name}: PARSE ERROR"
    | .ok pairs =>
      let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
      -- Build block set to identify return transitions
      let mut funcBlocks : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRipGuard ip_reg b.pc with
        | some src => funcBlocks := funcBlocks.insert src
        | none => pure ()
      -- Scan ALL body branches for stores of constants to the same address expression.
      -- The token variable (e.g., sym) is accessed through GOT dereference:
      --   store(val, load(mem, GOT_addr)) — same address expr, different constant vals.
      -- Group by (address expression hash) → collect distinct constant values.
      let mut storesByExprHash : Std.HashMap UInt64 (SymExpr Amd64Reg × Std.HashSet UInt64) := {}
      for b in bodyArr do
        match b.sub.mem with
        | .base => pure ()
        | _ =>
          -- Walk store chain, collect (addr_expr, const_value) pairs
          let mut mem := b.sub.mem
          let mut done := false
          while !done do
            match mem with
            | .store _w inner addr val =>
              -- Skip stack stores (addr uses rsp/rbp)
              let isStack := exprUsesRSP addr
              match resolveExprConst none val with
              | some constVal =>
                if !isStack then
                  let h := hash addr
                  let (expr, vals) := storesByExprHash.getD h (addr, {})
                  storesByExprHash := storesByExprHash.insert h (expr, vals.insert constVal)
              | none => pure ()
              mem := inner
            | .base => done := true
      -- Find the address expression with the most distinct values
      let mut bestHash : UInt64 := 0
      let mut bestCount : Nat := 0
      let mut bestExpr : Option (SymExpr Amd64Reg) := none
      for (h, (expr, vals)) in storesByExprHash.toArray do
        if vals.size > bestCount then
          bestHash := h
          bestCount := vals.size
          bestExpr := some expr
      -- Also check rax across all branches
      let mut raxVals : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRaxValueRaw b.sub with
        | some v => raxVals := raxVals.insert v
        | none => pure ()
      let (tokenVals, source) :=
        if bestCount >= raxVals.size && bestCount >= 2 then
          let (_, vals) := storesByExprHash.getD bestHash (SymExpr.const 0, {})
          (vals.toArray, s!"mem[{bestExpr.map (exprSummary · 3) |>.getD "?"}]")
        else if raxVals.size >= 2 then
          (raxVals.toArray, "rax")
        else
          (#[], "none")
      log s!"  {func.name}: {bodyArr.size} body branches, best_mem={bestCount} vals @ {bestExpr.map (exprSummary · 3) |>.getD "none"}, rax={raxVals.size} distinct"
      if tokenVals.size >= 2 then
        producers := producers.push (func.entryAddr, tokenVals)
        log s!"    → Producer candidate via {source} ({tokenVals.size} distinct values)"
  return producers

/-- Find consumer functions: those that call the producer in the call graph. -/
def findConsumers
    (functions : Array FunctionSpec)
    (callGraph : Array (UInt64 × UInt64))
    (producerAddr : UInt64)
    (log : String → IO Unit) :
    IO (Array FunctionSpec) := do
  let mut consumers : Array FunctionSpec := #[]
  for func in functions do
    if func.entryAddr == producerAddr then continue
    let callsProducer := callGraph.any fun (src, tgt) =>
      src == func.entryAddr && tgt == producerAddr
    if callsProducer then
      consumers := consumers.push func
      log s!"  Consumer: {func.name} @ {hexAddr func.entryAddr}"
  return consumers

/-- Check IsTokenConfig conditions: unique producer with ≥2 consumers.
    Returns the token config evidence or an error explaining why detection failed. -/
def checkTokenConfig
    (functions : Array FunctionSpec)
    (producers : Array (UInt64 × Array UInt64))
    (callGraph : Array (UInt64 × UInt64))
    (log : String → IO Unit) :
    IO (Except String TokenConfigEvidence) := do
  log s!"\n--- IsTokenConfig Check ---"
  if producers.isEmpty then
    log "  FAIL: No producer candidates (no function with ≥2 distinct rax values)"
    return .error "No producer function found"
  let mut validConfigs : Array TokenConfigEvidence := #[]
  for (addr, raxVals) in producers do
    let func := functions.find? fun f => f.entryAddr == addr
    match func with
    | some f =>
      let consumers ← findConsumers functions callGraph addr log
      if consumers.size >= 2 then
        log s!"  Producer {f.name}: {consumers.size} consumers — VALID"
        validConfigs := validConfigs.push {
          lexer := f
          raxValues := raxVals
          consumers := consumers
          callEdges := callGraph
        }
      else
        log s!"  Producer {f.name}: only {consumers.size} consumers — REJECTED (need ≥2)"
    | none => pure ()
  match validConfigs.size with
  | 0 =>
    log "  FAIL: No producer with ≥2 consumers"
    return .error "No producer with ≥2 consumers"
  | 1 =>
    log s!"  PASS: Unique producer {validConfigs[0]!.lexer.name} with {validConfigs[0]!.consumers.size} consumers"
    return .ok validConfigs[0]!
  | n =>
    log s!"  FAIL: Ambiguous — {n} producers each with ≥2 consumers"
    return .error s!"Ambiguous: {n} valid producers"

/-- Find entry point: the NT function not called by any other NT.
    Falls back to first NT if all are mutually recursive. -/
def findParserEntryPoint
    (ntFunctions : Array FunctionSpec)
    (callGraph : Array (UInt64 × UInt64))
    (log : String → IO Unit) :
    IO UInt64 := do
  let candidates := ntFunctions.filter fun f =>
    !(callGraph.any fun (src, tgt) =>
      tgt == f.entryAddr && (ntFunctions.any fun g => g.entryAddr == src))
  match candidates[0]? with
  | some f =>
    log s!"  Entry point: {f.name} (not called by any other NT)"
    return f.entryAddr
  | none =>
    match ntFunctions[0]? with
    | some f =>
      log s!"  Entry point: {f.name} (fallback — all NTs mutually recursive)"
      return f.entryAddr
    | none => return 0

/-- Classify functions: identify NTs (not lexer, transitively calls lexer).
    Returns (NTs, helpers). -/
def classifyParserFunctions
    (functions : Array FunctionSpec)
    (callGraph : Array (UInt64 × UInt64))
    (lexerAddr : UInt64)
    (log : String → IO Unit) :
    IO (Array FunctionSpec × Array FunctionSpec) := do
  log s!"\n--- Function Classification ---"
  let mut adj : Std.HashMap UInt64 (Array UInt64) := {}
  for (src, tgt) in callGraph do
    let arr := adj.getD src #[]
    adj := adj.insert src (arr.push tgt)
  let callsLexer (startAddr : UInt64) : Bool := Id.run do
    let mut visited : Std.HashSet UInt64 := {}
    let mut queue : Array UInt64 := #[startAddr]
    while !queue.isEmpty do
      let cur := queue.back!
      queue := queue.pop
      if visited.contains cur then continue
      visited := visited.insert cur
      if cur == lexerAddr then return true
      for tgt in adj.getD cur #[] do
        if !visited.contains tgt then
          queue := queue.push tgt
    return false
  let mut nts : Array FunctionSpec := #[]
  let mut helpers : Array FunctionSpec := #[]
  for func in functions do
    if func.entryAddr == lexerAddr then
      log s!"  {func.name}: LEXER"
    else
      let transCallsLex := callsLexer func.entryAddr
      if transCallsLex then
        nts := nts.push func
        log s!"  {func.name}: NT (transitively calls lexer)"
      else
        helpers := helpers.push func
        log s!"  {func.name}: HELPER (does not call lexer)"
  return (nts, helpers)

/-- Derive token names from the lexer's raw body branches.
    For each summary branch that stores a constant to the token variable,
    decode the data guard as CharClass. Uses summary branches (post-fixpoint)
    because multi-block character comparisons are composed into single guards. -/
def deriveTokenNames
    (lexerSpec : FunctionSpec)
    (summaryBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (log : String → IO Unit) :
    IO TokenNameTable := do
  let ip_reg := Amd64Reg.rip
  -- Use SUMMARY branches (post-fixpoint) for token name derivation.
  -- Summary branches have composed guards that include the full character class
  -- (multi-block paths are already collapsed).
  -- Step 1: Find the token variable address expression from summary branches.
  let mut storesByExprHash : Std.HashMap UInt64 (SymExpr Amd64Reg × Std.HashSet UInt64) := {}
  for b in summaryBranches do
    match b.sub.mem with
    | .base => pure ()
    | _ =>
      let mut mem := b.sub.mem
      let mut done := false
      while !done do
        match mem with
        | .store _w inner addr val =>
          let isStack := exprUsesRSP addr
          match resolveExprConst none val with
          | some constVal =>
            if !isStack then
              let h := hash addr
              let (expr, vals) := storesByExprHash.getD h (addr, {})
              storesByExprHash := storesByExprHash.insert h (expr, vals.insert constVal)
          | none => pure ()
          mem := inner
        | .base => done := true
  let mut bestHash : UInt64 := 0
  let mut bestCount : Nat := 0
  for (h, (_, vals)) in storesByExprHash.toArray do
    if vals.size > bestCount then
      bestHash := h
      bestCount := vals.size
  -- Step 2: For each summary branch that stores a constant to the token variable,
  -- extract the constant and decode the branch's data guard (character class).
  let mut table : TokenNameTable := {}
  if bestCount >= 2 then
    for b in summaryBranches do
      match b.sub.mem with
      | .base => pure ()
      | _ =>
        let mut mem := b.sub.mem
        let mut done := false
        while !done do
          match mem with
          | .store _w inner addr val =>
            let isStack := exprUsesRSP addr
            if !isStack && hash addr == bestHash then
              match resolveExprConst none val with
              | some constVal =>
                if !table.contains constVal then
                  let dataGuard := stripRipGuards ip_reg b.pc
                  let cc := (decodeCharClass dataGuard).simplify
                  -- Only add to table if we decoded a meaningful character class
                  -- (.any means we couldn't decode anything — no information)
                  match cc with
                  | .any => pure ()
                  | _ =>
                    let name := charClassToTokenName {} cc
                    table := table.insert constVal name
              | none => pure ()
            mem := inner
          | .base => done := true
  -- Fallback: try body-level rax extraction
  if table.size == 0 then
    match parseBlocksWithAddresses lexerSpec.blocks with
    | .error _ => pure ()
    | .ok pairs =>
      let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
      let mut lexerBlocks : Std.HashSet UInt64 := {}
      for b in bodyArr do
        match extractRipGuard ip_reg b.pc with
        | some src => lexerBlocks := lexerBlocks.insert src
        | none => pure ()
      for b in bodyArr do
        match extractRaxValueRaw b.sub with
        | some raxVal =>
          if table.contains raxVal then continue
          match extractRipTarget ip_reg b.sub with
          | some tgt =>
            if !lexerBlocks.contains tgt then
              let dataGuard := stripRipGuards ip_reg b.pc
              let cc := (decodeCharClass dataGuard).simplify
              match cc with
              | .any => pure ()
              | _ =>
                let name := charClassToTokenName {} cc
                table := table.insert raxVal name
          | none => pure ()
        | none => pure ()
  log s!"\n--- Derived Token Names ({table.size} entries) ---"
  for (code, name) in table.toArray do
    log s!"  {code.toNat} → {name}"
  return table

/-- Detect parser structure from converged function summaries.
    Uses IsTokenConfig (World 1, rax proxy) to identify lexer and NTs. -/
def detectParser
    (functions : Array FunctionSpec)
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (log : String → IO Unit) :
    IO (Except String ParserStructure) := do
  log "\n=== Parser Detection ==="
  let callGraph ← buildCallGraph functions log
  let producers ← findProducers functions summaries log
  match ← checkTokenConfig functions producers callGraph log with
  | .error e =>
    log s!"  Parser detection FAILED: {e}"
    return .error e
  | .ok evidence =>
    let (nts, _helpers) ← classifyParserFunctions functions callGraph evidence.lexer.entryAddr log
    let entryAddr ← findParserEntryPoint nts callGraph log
    let lexerSummary := summaries.getD evidence.lexer.entryAddr #[]
    let tokenNames ← deriveTokenNames evidence.lexer lexerSummary log
    let ps : ParserStructure := {
      classifiers := nts
      lexerName := evidence.lexer.name
      lexerAddr := evidence.lexer.entryAddr
      entryClassifier := entryAddr
      tokenNames := tokenNames
    }
    log s!"\n--- Parser Detection SUCCEEDED ---"
    log s!"  Lexer: {ps.lexerName} @ {hexAddr ps.lexerAddr}"
    log s!"  NTs: {nts.toList.map (·.name)}"
    log s!"  Entry: {hexAddr ps.entryClassifier}"
    log s!"  Token names: {ps.tokenNames.size} entries"
    return .ok ps

/-! ## EBNF Extraction from LTS

For each NT function, walk the LTS to produce EBNF productions:
- Transitions to lexer entry = terminal (token type from data guard label)
- Transitions to other NT entry = nonterminal reference
- Linear chains = sequence
- Branch points = alternatives
- Back edges = repetition

CRITICAL: alternatives are distinguished by BOTH target AND label.
This fixes term getting 2/3 — id and int both call next_sym but with
different character class labels (letters vs digits). -/

/-- An EBNF symbol: terminal token or nonterminal reference. -/
inductive GrammarSym where
  | terminal : CharClass → GrammarSym     -- raw guard, rendered via charClassToTokenName
  | nonterminal : String → GrammarSym     -- function name or synthetic loop NT
  deriving BEq, Hashable, Inhabited

def GrammarSym.isTerminal : GrammarSym → Bool
  | .terminal _ => true
  | .nonterminal _ => false

/-- Check if a CharClass is a single positive tokenCode. -/
def CharClass.isPositiveTokenCode : CharClass → Option UInt64
  | .tokenCode n => some n
  | _ => none

/-- DFS result: either completed productions, or a loop detected back to a target node. -/
inductive DFSResult where
  | productions : Array (Array GrammarSym) → DFSResult
  | loopDetected : UInt64 → Array GrammarSym → DFSResult  -- target, loop body

/-- DFS through LTS collecting ordered symbol sequences as grammar productions.
    Accumulates CharClass labels along internal transitions (accGuard) so that
    data guards from upstream comparison blocks classify tokens (e.g., id vs int).
    Loop recognition: back-edge detection via nodeStepIdx produces left-recursive
    productions: `funcName ++ steps[idx:]` (e.g., sum '+' term).
    Guard-based NT specialization: when calling an NT with accumulated guard that
    simplifies to a single positive tokenCode, emit terminal instead of nonterminal. -/
def ltsExtractProds
    (cur : UInt64)
    (steps : Array GrammarSym)
    (accGuard : CharClass)
    (ltsMap : Std.HashMap UInt64 (Array LTSTransition))
    (funcBlocks : Std.HashSet UInt64)
    (funcEntries : Std.HashMap UInt64 String)
    (visited : Std.HashSet UInt64)
    (nodeStepIdx : Std.HashMap UInt64 Nat)
    (funcName : String)
    (fuel : Nat)
    (bodyBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (lexerName : String := "next_sym")
    (tokenNames : TokenNameTable := {}) :
    Array (Array GrammarSym) :=
  match fuel with
  | 0 => #[steps]
  | fuel' + 1 => Id.run do
  if visited.contains cur then
    -- Back-edge detected: create left-recursive production
    match nodeStepIdx.get? cur with
    | some idx =>
      let loopBody := steps.extract idx steps.size
      if loopBody.isEmpty then return #[steps]
      else return #[#[.nonterminal funcName] ++ loopBody]
    | none => return #[steps]
  let visited' := visited.insert cur
  let nodeStepIdx' := nodeStepIdx.insert cur steps.size
  let edges := ltsMap.getD cur #[]
  if edges.isEmpty then
    return if steps.isEmpty then #[] else #[steps]
  let mut allPaths : Array (Array GrammarSym) := #[]
  for t in edges do
    let combinedGuard : CharClass := match accGuard, t.label with
      | .empty, _ | _, .empty => .empty
      | .any, l => l
      | g, .any => g
      | g, l => (CharClass.conj g l).simplify
    if combinedGuard == .empty then
      continue
    match funcEntries.get? t.tgt with
    | some "_exit" => pure ()
    | some callee =>
      -- External call: classify using accumulated guard
      let sym := if callee == lexerName then
          GrammarSym.terminal combinedGuard
        else
          -- Decision 1: positive tokenCode guard → emit terminal instead of NT
          match combinedGuard.isPositiveTokenCode with
          | some _ => GrammarSym.terminal combinedGuard
          | none => GrammarSym.nonterminal callee
      let steps' := steps.push sym
      let retAddr := bodyBranches.findSome? fun b =>
        match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
        | some src, some tgt =>
          if src == cur && tgt == t.tgt then extractCallReturn b.sub.mem else none
        | _, _ => none
      match retAddr with
      | some ret =>
        if funcBlocks.contains ret then
          allPaths := allPaths.append
            (ltsExtractProds ret steps' .any ltsMap funcBlocks funcEntries visited' nodeStepIdx' funcName fuel' bodyBranches lexerName tokenNames)
        else
          allPaths := allPaths.push steps'
      | none =>
        allPaths := allPaths.push steps'
    | none =>
      if funcBlocks.contains t.tgt then
        allPaths := allPaths.append
          (ltsExtractProds t.tgt steps combinedGuard ltsMap funcBlocks funcEntries visited' nodeStepIdx' funcName fuel' bodyBranches lexerName tokenNames)
      else
        -- Unknown external (helper like printf): preserve guard through call
        let retAddr := bodyBranches.findSome? fun b =>
          match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
          | some src, some tgt =>
            if src == cur && tgt == t.tgt then extractCallReturn b.sub.mem else none
          | _, _ => none
        match retAddr with
        | some ret =>
          if funcBlocks.contains ret then
            allPaths := allPaths.append
              (ltsExtractProds ret steps combinedGuard ltsMap funcBlocks funcEntries visited' nodeStepIdx' funcName fuel' bodyBranches lexerName tokenNames)
          else if !steps.isEmpty then
            allPaths := allPaths.push steps
        | none =>
          if !steps.isEmpty then
            allPaths := allPaths.push steps
  return allPaths

/-- BFS reachability in LTS (for finding orphan blocks). -/
def ltsReachable (entry : UInt64)
    (ltsMap : Std.HashMap UInt64 (Array LTSTransition))
    (funcBlocks : Std.HashSet UInt64)
    (_funcEntries : Std.HashMap UInt64 String)
    (bodyBranches : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) :
    Std.HashSet UInt64 := Id.run do
  let mut visited : Std.HashSet UInt64 := {}
  let mut queue : Array UInt64 := #[entry]
  while !queue.isEmpty do
    let cur := queue.back!
    queue := queue.pop
    if visited.contains cur then pure ()
    else
      visited := visited.insert cur
      for t in ltsMap.getD cur #[] do
        if funcBlocks.contains t.tgt && !visited.contains t.tgt then
          queue := queue.push t.tgt
        else
          let retAddr := bodyBranches.findSome? fun b =>
            match extractRipGuard Amd64Reg.rip b.pc, extractRipTarget Amd64Reg.rip b.sub with
            | some src, some tgt =>
              if src == cur && tgt == t.tgt then extractCallReturn b.sub.mem else none
            | _, _ => none
          match retAddr with
          | some ret =>
            if funcBlocks.contains ret && !visited.contains ret then
              queue := queue.push ret
          | none => pure ()
  return visited

/-- Render a GrammarSym as a string using the token name table. -/
def renderSym (tokenNames : TokenNameTable) : GrammarSym → String
  | .terminal cc => charClassToTokenName tokenNames cc
  | .nonterminal name => name

/-- Format a production RHS as a space-separated string. -/
def formatProd (tokenNames : TokenNameTable) (syms : Array GrammarSym) : String :=
  if syms.isEmpty then "ε"
  else " ".intercalate (syms.toList.map (renderSym tokenNames))

/-- Extracted grammar for one NT: productions + optional repetition NT. -/
structure ExtractedNTGrammar where
  funcName : String
  prods : Array (Array GrammarSym)
  repNTName : Option String                          -- e.g., "statement_rep"
  repNTProds : Array (Array GrammarSym)              -- e.g., [statement], [statement, statement_rep]

/-- Extract grammar productions for one NT function.
    Returns productions + optional factored repetition NT. -/
def extractNTGrammar
    (funcName : String) (entryAddr : UInt64)
    (bodyArr : Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))
    (funcEntries : Std.HashMap UInt64 String)
    (lexerName : String := "next_sym")
    (tokenNames : TokenNameTable := {}) : ExtractedNTGrammar := Id.run do
  let ip_reg := Amd64Reg.rip
  let lts := extractLTS ip_reg bodyArr funcEntries
  let mut ltsMap : Std.HashMap UInt64 (Array LTSTransition) := {}
  let mut funcBlocks : Std.HashSet UInt64 := {}
  for b in bodyArr do
    match extractRipGuard ip_reg b.pc with
    | some src => funcBlocks := funcBlocks.insert src
    | none => pure ()
  for t in lts.transitions do
    let arr := ltsMap.getD t.src #[]
    ltsMap := ltsMap.insert t.src (arr.push t)
  -- Main DFS from entry
  let rawPaths := ltsExtractProds entryAddr #[] .any ltsMap funcBlocks funcEntries {} {} funcName 61 bodyArr lexerName tokenNames
  -- Orphan blocks: not reachable from entry, contain NT calls
  let reachable := ltsReachable entryAddr ltsMap funcBlocks funcEntries bodyArr
  let mut orphanPaths : Array (Array GrammarSym) := #[]
  for (src, edges) in ltsMap.toArray do
    if reachable.contains src then pure ()
    else
      for t in edges do
        match funcEntries.get? t.tgt with
        | some "_exit" => pure ()
        | some callee =>
          if callee == lexerName then pure ()
          else
            let retAddr := bodyArr.findSome? fun b =>
              match extractRipGuard ip_reg b.pc, extractRipTarget ip_reg b.sub with
              | some s, some tgt =>
                if s == src && tgt == t.tgt then extractCallReturn b.sub.mem else none
              | _, _ => none
            match retAddr with
            | some ret =>
              if funcBlocks.contains ret then
                orphanPaths := orphanPaths.append
                  (ltsExtractProds ret #[.nonterminal callee] .any ltsMap funcBlocks funcEntries {} {} funcName 61 bodyArr lexerName tokenNames)
            | none => pure ()
        | none => pure ()
  -- Deduplicate using rendered strings
  let mut seen : Std.HashSet String := {}
  let mut deduped : Array (Array GrammarSym) := #[]
  for p in rawPaths.append orphanPaths do
    let key := formatProd tokenNames p
    if !seen.contains key then
      seen := seen.insert key
      deduped := deduped.push p
  -- Post-process: factor self-repetition into repetition NT.
  -- Detect pattern: [funcName, funcName] production (self-recursive loop body)
  -- paired with a two-terminal production [T1, T2] (delimiter frame).
  -- Merge into: [T1, repNT, T2] with repNT → funcName | funcName repNT.
  let hasSelfRep := deduped.any fun p =>
    p.size == 2 && p[0]! == .nonterminal funcName && p[1]! == .nonterminal funcName
  if hasSelfRep then
    let repName := funcName ++ "_rep"
    let repProds : Array (Array GrammarSym) := #[
      #[.nonterminal funcName],
      #[.nonterminal funcName, .nonterminal repName]
    ]
    let isTwoTerminals (p : Array GrammarSym) : Bool :=
      p.size == 2 && p[0]!.isTerminal && p[1]!.isTerminal
    let modified := deduped.filterMap fun p =>
      if p.size == 2 && p[0]! == .nonterminal funcName && p[1]! == .nonterminal funcName then
        none
      else if isTwoTerminals p then
        some #[p[0]!, .nonterminal repName, p[1]!]
      else some p
    return { funcName := funcName, prods := modified, repNTName := some repName, repNTProds := repProds }
  else
    return { funcName := funcName, prods := deduped, repNTName := none, repNTProds := #[] }

/-- Structural comparison of extracted grammar against golden grammar.
    Builds terminal and NT mappings, then checks production-level isomorphism. -/
def structuralGoldenCompare (log : String → IO Unit)
    (grammars : Array ExtractedNTGrammar)
    (tokenNames : TokenNameTable)
    (golden : Std.HashMap String (List (List String)) := goldenProds) : IO Unit := do
  -- Collect all known NT names (function NTs + synthetic rep NTs)
  let mut allNTNames : Std.HashSet String := {}
  for g in grammars do
    allNTNames := allNTNames.insert g.funcName
    match g.repNTName with
    | some n => allNTNames := allNTNames.insert n
    | none => pure ()
  -- Golden NTs: keys of golden prods
  let goldenNTNames : Std.HashSet String :=
    golden.toArray.foldl (fun s (k, _) => s.insert k) {}
  for n in goldenNTNames do
    allNTNames := allNTNames.insert n
  -- Synthetic NTs: golden NTs not in extracted function NTs (e.g., "statements")
  let funcNTNames : Std.HashSet String :=
    grammars.foldl (fun s g => s.insert g.funcName) {}
  let syntheticGoldenNTs := goldenNTNames.toArray.filter fun n => !funcNTNames.contains n
  -- Map synthetic rep NTs to golden synthetic NTs
  let repNTs := grammars.filterMap fun g => g.repNTName
  let mut ntMapping : Std.HashMap String String := {}
  for i in [:repNTs.size.min syntheticGoldenNTs.size] do
    ntMapping := ntMapping.insert repNTs[i]! syntheticGoldenNTs[i]!
  -- Helper: check if a symbol name is a known NT (not a terminal)
  let isNT (name : String) : Bool := allNTNames.contains name
  -- Build terminal mapping by scanning UNMATCHED productions only.
  -- First remove exact matches, then build mappings from remaining pairs.
  let mut termMapping : Std.HashMap String String := {}
  let mut prodGoldenPairs : Array (Array (Array GrammarSym) × List (List String)) := #[]
  for g in grammars do
    prodGoldenPairs := prodGoldenPairs.push (g.prods, golden.getD g.funcName [])
    match g.repNTName with
    | some repName =>
      let goldenName := ntMapping.getD repName repName
      prodGoldenPairs := prodGoldenPairs.push (g.repNTProds, golden.getD goldenName [])
    | none => pure ()
  for (prods, goldenEntry) in prodGoldenPairs do
    -- Phase 1: remove exact matches from both pools
    let mut remainGolden : List (List String) := goldenEntry
    let mut unmatchedProds : Array (Array GrammarSym) := #[]
    for prod in prods do
      let rendered := prod.toList.map fun sym => match sym with
        | .terminal cc => charClassToTokenName tokenNames cc
        | .nonterminal n => ntMapping.getD n n
      let renderedStr := " ".intercalate rendered
      let exactMatch := remainGolden.any fun gp => " ".intercalate gp == renderedStr
      if exactMatch then
        remainGolden := remainGolden.filter fun gp => " ".intercalate gp != renderedStr
      else
        unmatchedProds := unmatchedProds.push prod
    -- Phase 2: build mappings from unmatched pairs
    for prod in unmatchedProds do
      let rendered := prod.toList.map fun sym => match sym with
        | .terminal cc => charClassToTokenName tokenNames cc
        | .nonterminal n => ntMapping.getD n n
      for gProd in remainGolden do
        if rendered.length == gProd.length then
          let pairs := rendered.zip gProd
          let allMatch := pairs.all fun (e, g) =>
            e == g || (!isNT e && !isNT g)
          if allMatch then
            for (e, g) in pairs do
              if e != g && !isNT e && !isNT g then
                termMapping := termMapping.insert e g
  -- Apply both mappings and count matches
  log "\n=== Structural Grammar Comparison ==="
  if !termMapping.isEmpty then
    let termPairs := termMapping.toArray.map fun (e, g) => s!"{e} ↔ {g}"
    log s!"  Terminal mapping: {", ".intercalate termPairs.toList}"
  if !ntMapping.isEmpty then
    let ntPairs := ntMapping.toArray.map fun (e, g) => s!"{e} ↔ {g}"
    log s!"  NT mapping: {", ".intercalate ntPairs.toList}"
  let mut totalMatch : Nat := 0
  let mut totalGolden : Nat := 0
  let mut totalExtra : Nat := 0
  for g in grammars do
    let goldenForFunc := golden.getD g.funcName []
    let goldenSet : Std.HashSet String :=
      goldenForFunc.foldl (fun s gp => s.insert (" ".intercalate gp)) {}
    -- Render extracted productions with mappings applied
    let mut matchCount : Nat := 0
    let mut extraCount : Nat := 0
    for prod in g.prods do
      let rendered := prod.toList.map fun sym => match sym with
        | .terminal cc =>
          let raw := charClassToTokenName tokenNames cc
          termMapping.getD raw raw
        | .nonterminal n => ntMapping.getD n n
      let renderedStr := " ".intercalate rendered
      if goldenSet.contains renderedStr then
        matchCount := matchCount + 1
      else
        extraCount := extraCount + 1
    -- Also check rep NT productions
    match g.repNTName with
    | some repName =>
      let goldenName := ntMapping.getD repName repName
      let repGolden := golden.getD goldenName []
      let repGoldenSet : Std.HashSet String :=
        repGolden.foldl (fun s gp => s.insert (" ".intercalate gp)) {}
      let mut repMatch : Nat := 0
      for prod in g.repNTProds do
        let rendered := prod.toList.map fun sym => match sym with
          | .terminal cc =>
            let raw := charClassToTokenName tokenNames cc
            termMapping.getD raw raw
          | .nonterminal n => ntMapping.getD n n
        let renderedStr := " ".intercalate rendered
        if repGoldenSet.contains renderedStr then
          repMatch := repMatch + 1
      let repTotal := repGolden.length
      let mark := if repMatch == repTotal && repTotal > 0 then " ✓" else ""
      log s!"  {repName} ({goldenName}): {repMatch}/{repTotal}{mark}"
      totalMatch := totalMatch + repMatch
      totalGolden := totalGolden + repTotal
    | none => pure ()
    let mark := if matchCount == goldenForFunc.length && goldenForFunc.length > 0 then " ✓" else ""
    log s!"  {g.funcName}: {matchCount}/{goldenForFunc.length}{mark}"
    if extraCount > 0 then
      log s!"    ({extraCount} extra productions)"
    totalMatch := totalMatch + matchCount
    totalGolden := totalGolden + goldenForFunc.length
    totalExtra := totalExtra + extraCount
  let mark := if totalMatch == totalGolden then " ✓" else ""
  log s!"  Total: {totalMatch}/{totalGolden}{mark}"
  if totalExtra > 0 then
    log s!"  ({totalExtra} extra productions total)"

/-- Print EBNF grammar for all NT functions using LTS-based extraction.
    Uses ParserStructure for lexer identification and token names when available. -/
def printLTSGrammar (log : String → IO Unit)
    (functions : Array FunctionSpec)
    (funcEntries : Std.HashMap UInt64 String)
    (_summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))))
    (parserStructure : Option ParserStructure := none)
    (golden : Std.HashMap String (List (List String)) := goldenProds) : IO Unit := do
  let ip_reg := Amd64Reg.rip
  let (tokenNames, lexerName, lexerAddr) := match parserStructure with
    | some ps => (ps.tokenNames, ps.lexerName, ps.lexerAddr)
    | none => (({} : TokenNameTable), "next_sym", (0 : UInt64))
  log s!"\n=== Token Name Table ({tokenNames.size} entries, derived={parserStructure.isSome}) ==="
  for (code, name) in tokenNames.toArray do
    log s!"  {code.toNat} → {name}"
  -- Extract grammar for detected NT classifiers (or all non-lexer if no ParserStructure)
  let classifierAddrs : Option (Std.HashSet UInt64) := match parserStructure with
    | some ps => some (ps.classifiers.foldl (fun s f => s.insert f.entryAddr) {})
    | none => none
  let mut grammars : Array ExtractedNTGrammar := #[]
  for func in functions do
    if func.entryAddr == lexerAddr then continue
    -- When parser structure detected, only extract for classifier NTs
    match classifierAddrs with
    | some addrs => if !addrs.contains func.entryAddr then continue
    | none => pure ()
    -- Skip lexer by name for backward compatibility when no ParserStructure
    if parserStructure.isNone && func.name == "next_sym" then continue
    match parseBlocksWithAddresses func.blocks with
    | .error e => log s!"  Parse error for {func.name}: {e}"
    | .ok pairs =>
      let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
      grammars := grammars.push (extractNTGrammar func.name func.entryAddr bodyArr funcEntries lexerName tokenNames)
  -- Print raw extracted grammar
  log "\n=== EBNF Grammar (LTS-based extraction) ==="
  for g in grammars do
    log s!"\n  {g.funcName}:"
    for prod in g.prods do
      log s!"    {g.funcName} -> {formatProd tokenNames prod}"
    match g.repNTName with
    | some repName =>
      log s!"    -- Repetition NT: {repName}"
      for prod in g.repNTProds do
        log s!"    {repName} -> {formatProd tokenNames prod}"
    | none => pure ()
  -- Structural comparison against golden grammar
  structuralGoldenCompare log grammars tokenNames golden

/-! ## Run stabilization -/

/-- Build funcEntries map from function specs. -/
def buildFuncEntries (functions : Array FunctionSpec) : Std.HashMap UInt64 String :=
  functions.foldl (fun m f => m.insert f.entryAddr f.name) {}

/-- Run the full pipeline on a set of function specs: fixpoint → detect → extract.
    The generic pipeline used by both legacy and file-based entry points.
    When golden prods are provided, structural comparison is run against them. -/
def runPipeline (functions : Array FunctionSpec) (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (golden : Std.HashMap String (List (List String)) := goldenProds) : IO Unit := do
  log "=== Stratified Dispatch Loop Stabilization ==="
  let summaries ← stratifiedFixpoint functions regions log
  let funcEntries := buildFuncEntries functions
  -- Parser detection
  let parserResult ← detectParser functions summaries log
  let ps := match parserResult with
    | .ok ps => some ps
    | .error _ => none
  -- EBNF extraction for parser NTs (LTS-based)
  printLTSGrammar log functions funcEntries summaries ps golden

/-- Main entry point using file-based input: blocks.json + ELF binary.
    Loads blocks from JSON, reads symbols from ELF, discovers functions, runs pipeline. -/
def dispatchLoopEvalFromFiles (blocksJson : System.FilePath) (elfBinary : System.FilePath)
    (log : String → IO Unit) : IO Unit := do
  log s!"Loading blocks from {blocksJson}..."
  let blocks ← loadBlocksFromJSON blocksJson
  log s!"  {blocks.size} blocks loaded"
  log s!"Reading symbols from {elfBinary}..."
  let symbols ← ElfSymbolTable.readSymbolsFromFile elfBinary
  log s!"  {symbols.size} function symbols found"
  for (name, addr, size) in symbols do
    log s!"    {name} @ 0x{String.ofList (Nat.toDigits 16 addr.toNat)}, {size} bytes"
  match discoverFunctions blocks symbols with
  | .error e => log s!"Function discovery error: {e}"
  | .ok result =>
    log s!"Discovered {result.functions.size} functions with blocks:"
    for f in result.functions do
      log s!"  {f.name}: {f.blocks.length} blocks"
    if result.orphanCount > 0 then
      log s!"  WARNING: {result.orphanCount} blocks not in any function symbol range"
    runPipeline result.functions (log := log)

/-- Standard log function: writes to both stdout and a log file. -/
def mkLogger (logPath : System.FilePath) : IO (String → IO Unit) := do
  IO.FS.writeFile logPath ""
  return fun msg => do
    IO.println msg
    let h ← IO.FS.Handle.mk logPath .append
    h.putStrLn msg

def mkFileLogger (logPath : System.FilePath) : IO (String → IO Unit) := do
  IO.FS.writeFile logPath ""
  return fun msg => do
    let h ← IO.FS.Handle.mk logPath .append
    h.putStrLn msg

/-! ## JSON Output -/

/-- Serialize extracted pipeline results to structured JSON.
    Includes: functions, parser structure, grammar, and LTS. -/
def pipelineToJson (functions : Array FunctionSpec)
    (parserStructure : Option ParserStructure) : Lean.Json :=
  let ip_reg := Amd64Reg.rip
  let (tokenNames, lexerName, lexerAddr) := match parserStructure with
    | some ps => (ps.tokenNames, ps.lexerName, ps.lexerAddr)
    | none => (({} : TokenNameTable), "next_sym", (0 : UInt64))
  let funcEntries := functions.foldl (fun m f => m.insert f.entryAddr f.name)
    ({} : Std.HashMap UInt64 String)
  -- Extract grammars (pure computation)
  let classifierAddrs : Option (Std.HashSet UInt64) := match parserStructure with
    | some ps => some (ps.classifiers.foldl (fun s f => s.insert f.entryAddr) {})
    | none => none
  let grammars : Array ExtractedNTGrammar := Id.run do
    let mut gs : Array ExtractedNTGrammar := #[]
    for func in functions do
      let skip := func.entryAddr == lexerAddr ||
        (parserStructure.isNone && func.name == "next_sym") ||
        (match classifierAddrs with | some addrs => !addrs.contains func.entryAddr | none => false)
      if !skip then
        match parseBlocksWithAddresses func.blocks with
        | .error _ => pure ()
        | .ok pairs =>
          let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
          gs := gs.push (extractNTGrammar func.name func.entryAddr bodyArr funcEntries
                          lexerName tokenNames)
    gs
  -- Functions array
  let funcsJson := Lean.Json.arr (functions.map fun f =>
    Lean.Json.mkObj [
      ("name", .str f.name),
      ("entryAddr", .str (hexAddr f.entryAddr)),
      ("blockCount", .num ⟨f.blocks.length, 0⟩)
    ])
  -- Parser structure
  let parserJson := match parserStructure with
    | some ps => Lean.Json.mkObj [
        ("detected", .bool true),
        ("lexer", .str ps.lexerName),
        ("lexerAddr", .str (hexAddr ps.lexerAddr)),
        ("entryClassifier", .str (hexAddr ps.entryClassifier)),
        ("tokenNames", Lean.Json.mkObj (ps.tokenNames.toArray.toList.map fun (code, name) =>
          (s!"{code.toNat}", .str name)))
      ]
    | none => Lean.Json.mkObj [("detected", .bool false)]
  -- Grammar per NT
  let grammarEntries : List (String × Lean.Json) := Id.run do
    let mut entries : List (String × Lean.Json) := []
    for g in grammars do
      let prods := g.prods.map fun prod =>
        Lean.Json.arr (prod.map fun sym => .str (renderSym tokenNames sym))
      entries := entries ++ [(g.funcName, Lean.Json.mkObj [
        ("productions", Lean.Json.arr prods)
      ])]
      match g.repNTName with
      | some repName =>
        let repProds := g.repNTProds.map fun prod =>
          Lean.Json.arr (prod.map fun sym => .str (renderSym tokenNames sym))
        entries := entries ++ [(repName, Lean.Json.mkObj [
          ("productions", Lean.Json.arr repProds)
        ])]
      | none => pure ()
    entries
  let grammarJson := Lean.Json.mkObj grammarEntries
  -- LTS per NT function
  let ltsEntries : List (String × Lean.Json) := Id.run do
    let mut entries : List (String × Lean.Json) := []
    for g in grammars do
      match functions.find? (·.name == g.funcName) with
      | none => pure ()
      | some f =>
        match parseBlocksWithAddresses f.blocks with
        | .error _ => pure ()
        | .ok pairs =>
          let bodyArr := finsetToArray (flatBodyDenot ip_reg pairs)
          let lts := extractLTS ip_reg bodyArr funcEntries
          let transJson := lts.transitions.map fun t =>
            Lean.Json.mkObj [
              ("src", .str (hexAddr t.src)),
              ("label", .str (charClassToTokenName tokenNames t.label)),
              ("tgt", .str (hexAddr t.tgt))
            ]
          entries := entries ++ [(f.name, Lean.Json.mkObj [
            ("transitions", Lean.Json.arr transJson),
            ("stateCount", .num ⟨lts.states.size, 0⟩),
            ("transitionCount", .num ⟨lts.transitions.size, 0⟩)
          ])]
    entries
  let ltsJson := Lean.Json.mkObj ltsEntries
  -- Top-level result
  Lean.Json.mkObj [
    ("functions", funcsJson),
    ("parser", parserJson),
    ("grammar", grammarJson),
    ("lts", ltsJson)
  ]

/-- Run pipeline and output structured JSON to stdout. Log goes to file only. -/
def runPipelineJSON (functions : Array FunctionSpec) (regions : Array MemRegion := #[])
    (log : String → IO Unit) : IO Unit := do
  log "=== Stratified Dispatch Loop Stabilization (JSON mode) ==="
  let summaries ← stratifiedFixpoint functions regions log
  let parserResult ← detectParser functions summaries log
  let ps := match parserResult with
    | .ok ps => some ps
    | .error _ => none
  let json := pipelineToJson functions ps
  IO.println json.pretty

/-! ## Entry-point scoping -/

/-- BFS reachability from an entry address in a call graph. Pure computation. -/
def callGraphReachable (entryAddr : UInt64) (callGraph : Array (UInt64 × UInt64)) :
    Std.HashSet UInt64 := Id.run do
  let mut reachable : Std.HashSet UInt64 := {}
  let mut queue : Array UInt64 := #[entryAddr]
  while !queue.isEmpty do
    let cur := queue.back!
    queue := queue.pop
    if reachable.contains cur then pure ()
    else
      reachable := reachable.insert cur
      for (src, tgt) in callGraph do
        if src == cur && !reachable.contains tgt then
          queue := queue.push tgt
  return reachable

/-- Given an entry address, compute the transitive closure of the call graph
    and return only the functions reachable from that entry.
    Uses buildCallGraph (syntactic, no fixpoint needed). -/
def scopeByEntry (functions : Array FunctionSpec) (entryAddr : UInt64)
    (log : String → IO Unit) : IO (Array FunctionSpec) := do
  let callGraph ← buildCallGraph functions log
  let reachable := callGraphReachable entryAddr callGraph
  let result := functions.filter fun f => reachable.contains f.entryAddr
  log s!"\n=== Entry-point scoping from {hexAddr entryAddr} ==="
  log s!"  {result.size}/{functions.size} functions reachable"
  for f in result do
    log s!"    {f.name} @ {hexAddr f.entryAddr}"
  return result

/-- Resolve an entry point: by hex address or by function name. -/
def resolveEntry (functions : Array FunctionSpec) (entry : String) : Option UInt64 :=
  -- Try as hex address first
  match parseHexAddr entry with
  | some addr => if functions.any (·.entryAddr == addr) then some addr else none
  | none =>
    -- Try as function name
    match functions.find? (·.name == entry) with
    | some f => some f.entryAddr
    | none => none

/-! ## CLI Argument Parsing -/

/-- Parsed CLI configuration. -/
structure CLIConfig where
  jsonPath : Option System.FilePath := none
  elfBinary : Option System.FilePath := none
  jsonOutput : Bool := false
  functionsSpec : Option String := none  -- comma-separated names or addrs
  entry : Option String := none
  logPath : System.FilePath := ".lake/stabilization.log"
  showHelp : Bool := false
  deriving Inhabited

/-- Parse comma-separated hex addresses. -/
private def parseAddrList (s : String) : Option (Array UInt64) :=
  let parts := s.splitOn ","
  let parsed := parts.filterMap fun p => parseHexAddr p.trimAscii.toString
  if parsed.length == parts.length then some parsed.toArray else none

/-- Resolve a comma-separated list of function names or addresses to FunctionSpecs.
    Returns the subset of functions matching the given names/addresses. -/
def resolveFunctionList (functions : Array FunctionSpec) (spec : String) : Array FunctionSpec :=
  let parts := spec.splitOn ","
  let names := parts.map (·.trimAscii.toString)
  functions.filter fun f =>
    names.any fun n =>
      f.name == n || (match parseHexAddr n with | some a => f.entryAddr == a | none => false)

/-- Parse CLI arguments into a CLIConfig. -/
private def parseCLIArgs : List String → CLIConfig → CLIConfig
  | [], cfg => cfg
  | "--help" :: rest, cfg => parseCLIArgs rest { cfg with showHelp := true }
  | "-h" :: rest, cfg => parseCLIArgs rest { cfg with showHelp := true }
  | "--json" :: rest, cfg => parseCLIArgs rest { cfg with jsonOutput := true }
  | "--functions" :: spec :: rest, cfg =>
    parseCLIArgs rest { cfg with functionsSpec := some spec }
  | "--entry" :: name :: rest, cfg => parseCLIArgs rest { cfg with entry := some name }
  | "--log" :: path :: rest, cfg => parseCLIArgs rest { cfg with logPath := path }
  | arg :: rest, cfg =>
    if arg.startsWith "--" then
      parseCLIArgs rest cfg  -- skip unknown flags
    else if cfg.jsonPath.isNone then
      parseCLIArgs rest { cfg with jsonPath := some arg }
    else if cfg.elfBinary.isNone then
      parseCLIArgs rest { cfg with elfBinary := some arg }
    else
      parseCLIArgs rest cfg  -- extra positional args ignored

/-- Print usage/help text. -/
private def printUsage : IO Unit := do
  IO.eprintln "Usage: dispatchLoopEval [OPTIONS] <input.json> [elf-binary]"
  IO.eprintln "       dispatchLoopEval --test [--subject NAME]"
  IO.eprintln ""
  IO.eprintln "Extract grammars from binary dispatch loops via symbolic execution."
  IO.eprintln ""
  IO.eprintln "Arguments:"
  IO.eprintln "  <input.json>         Per-function blocks JSON (VEX IR)"
  IO.eprintln "  [elf-binary]         ELF binary for symbol-based function discovery"
  IO.eprintln ""
  IO.eprintln "Options:"
  IO.eprintln "  --json               Output results as structured JSON to stdout"
  IO.eprintln "  --entry NAME|ADDR    Scope to functions reachable from entry point"
  IO.eprintln "  --functions ADDRS    Comma-separated hex entry addresses to analyze"
  IO.eprintln "  --log PATH           Log file path (default: .lake/stabilization.log)"
  IO.eprintln "  --test               Run test suite (via dispatchLoopTest)"
  IO.eprintln "  --subject NAME       Run specific test subject (with --test)"
  IO.eprintln "  --help, -h           Show this help message"
  IO.eprintln ""
  IO.eprintln "Examples:"
  IO.eprintln "  dispatchLoopEval reference/tinyc/blocks.json --entry statement"
  IO.eprintln "  dispatchLoopEval reference/tinyc/blocks.json --entry 0x400678 --json"
  IO.eprintln "  dispatchLoopEval blocks.json tiny.o --functions 0x401234,0x401567"
  IO.eprintln "  dispatchLoopEval --test"

/-- Main entry point for dispatch loop evaluation with CLI args. -/
def dispatchLoopEvalMain (args : List String := []) : IO Unit := do
  let cfg := parseCLIArgs args {}
  if cfg.showHelp then
    printUsage
    return
  match cfg.jsonPath with
  | none =>
    printUsage
    IO.Process.exit 1
  | some jsonPath =>
    let log ← if cfg.jsonOutput
              then mkFileLogger cfg.logPath
              else mkLogger cfg.logPath
    match cfg.elfBinary with
    | some elfBinary =>
      -- File-based mode: blocks.json + ELF binary
      log s!"Loading blocks from {jsonPath}..."
      let blocks ← loadBlocksFromJSON jsonPath
      log s!"  {blocks.size} blocks loaded"
      log s!"Reading symbols from {elfBinary}..."
      let symbols ← ElfSymbolTable.readSymbolsFromFile elfBinary
      log s!"  {symbols.size} function symbols found"
      for (name, addr, size) in symbols do
        log s!"    {name} @ 0x{String.ofList (Nat.toDigits 16 addr.toNat)}, {size} bytes"
      match discoverFunctions blocks symbols with
      | .error e =>
        IO.eprintln s!"Function discovery error: {e}"
        IO.Process.exit 1
      | .ok result =>
        log s!"Discovered {result.functions.size} functions with blocks:"
        for f in result.functions do
          log s!"  {f.name}: {f.blocks.length} blocks"
        if result.orphanCount > 0 then
          log s!"  WARNING: {result.orphanCount} blocks not in any function symbol range"
        -- Scope functions: --entry then --functions
        let functions ← match cfg.entry with
          | some entry =>
            match resolveEntry result.functions entry with
            | some addr => scopeByEntry result.functions addr log
            | none =>
              IO.eprintln s!"Unknown entry point: {entry}"
              IO.Process.exit 1
          | none => pure result.functions
        let functions := match cfg.functionsSpec with
          | some spec => resolveFunctionList functions spec
          | none => functions
        if cfg.jsonOutput then
          runPipelineJSON functions (log := log)
        else
          runPipeline functions (log := log)
    | none =>
      -- Single JSON: per-function format
      log s!"Loading functions from {jsonPath}..."
      let (allFunctions, regions) ← loadFunctionsFromJSON jsonPath
      log s!"  {allFunctions.size} functions loaded, {regions.size} memory regions"
      for r in regions do
        log s!"    {r.name}: [0x{String.ofList (Nat.toDigits 16 r.vaddr.toNat)}, +{r.size}) {r.flags}"
      -- Scope functions: --entry (call graph reachability) then --functions (exact set)
      let functions ← match cfg.entry with
        | some entry =>
          match resolveEntry allFunctions entry with
          | some addr => scopeByEntry allFunctions addr log
          | none =>
            IO.eprintln s!"Unknown entry point: {entry}"
            IO.eprintln s!"Available: {", ".intercalate (allFunctions.map (·.name)).toList}"
            IO.Process.exit 1
        | none => pure allFunctions
      let functions := match cfg.functionsSpec with
        | some spec =>
          let filtered := resolveFunctionList functions spec
          filtered
        | none => functions
      if cfg.jsonOutput then
        runPipelineJSON functions regions log
      else
        runPipeline functions regions log
