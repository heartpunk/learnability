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
  | .ite c t f => 1 + exprNodeCount c + exprNodeCount t + exprNodeCount f
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
  | .ite c t f => exprUnresolvedLoads c + exprUnresolvedLoads t + exprUnresolvedLoads f
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
  | .ite c t f, d => s!"ite({exprSummary c (d-1)},{exprSummary t (d-1)},{exprSummary f (d-1)})"
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

/-- Check if two addresses are in different regions (non-aliasing). -/
private def regionNonAliasing {Reg : Type} [DecidableEq Reg]
    (clf : AddrClassifier Reg) (storeAddr loadAddr : SymExpr Reg) : Bool :=
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
  if constStackSkip || stackConstSkip then true
  else
    match (clf storeAddr, clf loadAddr) with
    | (some sr, some lr) => sr != lr
    | _ => false

def rawConstRangesNonOverlapping (a : UInt64) (aw : Nat) (b : UInt64) (bw : Nat) : Bool :=
  a.toNat + aw ≤ UInt64.size ∧
  b.toNat + bw ≤ UInt64.size ∧
  (a.toNat + aw ≤ b.toNat ∨ b.toNat + bw ≤ a.toNat)

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
        if rawConstRangesNonOverlapping a storeWidth.byteCount b loadWidth.byteCount then
          resolveLoadFrom loadWidth innerMem loadAddr classify  -- non-overlapping, skip store
        else
          .load loadWidth mem loadAddr  -- overlapping or wrapping, keep as-is
      -- reg+const vs reg+const: same base register, different constant offsets.
      | (.add64 r1 (.const c1), .add64 r2 (.const c2)) =>
        if r1 == r2 && rawConstRangesNonOverlapping c1 storeWidth.byteCount c2 loadWidth.byteCount then
          resolveLoadFrom loadWidth innerMem loadAddr classify
        else
          match classify with
          | some clf => if regionNonAliasing clf storeAddr loadAddr then
              resolveLoadFrom loadWidth innerMem loadAddr (some clf)
            else .load loadWidth mem loadAddr
          | none => .load loadWidth mem loadAddr
      | (.sub64 r1 (.const c1), .sub64 r2 (.const c2)) =>
        let a := (0 : UInt64) - c1; let b := (0 : UInt64) - c2
        if r1 == r2 && rawConstRangesNonOverlapping a storeWidth.byteCount b loadWidth.byteCount then
          resolveLoadFrom loadWidth innerMem loadAddr classify
        else
          match classify with
          | some clf => if regionNonAliasing clf storeAddr loadAddr then
              resolveLoadFrom loadWidth innerMem loadAddr (some clf)
            else .load loadWidth mem loadAddr
          | none => .load loadWidth mem loadAddr
      | (.add64 r1 (.const c1), .sub64 r2 (.const c2)) =>
        let b := (0 : UInt64) - c2
        if r1 == r2 && rawConstRangesNonOverlapping c1 storeWidth.byteCount b loadWidth.byteCount then
          resolveLoadFrom loadWidth innerMem loadAddr classify
        else
          match classify with
          | some clf => if regionNonAliasing clf storeAddr loadAddr then
              resolveLoadFrom loadWidth innerMem loadAddr (some clf)
            else .load loadWidth mem loadAddr
          | none => .load loadWidth mem loadAddr
      | (.sub64 r1 (.const c1), .add64 r2 (.const c2)) =>
        let a := (0 : UInt64) - c1
        if r1 == r2 && rawConstRangesNonOverlapping a storeWidth.byteCount c2 loadWidth.byteCount then
          resolveLoadFrom loadWidth innerMem loadAddr classify
        else
          match classify with
          | some clf => if regionNonAliasing clf storeAddr loadAddr then
              resolveLoadFrom loadWidth innerMem loadAddr (some clf)
            else .load loadWidth mem loadAddr
          | none => .load loadWidth mem loadAddr
      | _ =>
        -- Non-constant, non-reg+const addresses: fall back to region-based non-aliasing
        match classify with
        | some clf => if regionNonAliasing clf storeAddr loadAddr then
              resolveLoadFrom loadWidth innerMem loadAddr (some clf)
            else .load loadWidth mem loadAddr
        | none => .load loadWidth mem loadAddr

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
  | .ite c t f => .ite (simplifyLoadStoreExpr c) (simplifyLoadStoreExpr t) (simplifyLoadStoreExpr f)
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
  | .shr64 a b => .shr64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .mul64 a b => .mul64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .mul32 a b => .mul32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .sar64 a b => .sar64 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
  | .sar32 a b => .sar32 (simplifyLoadStoreExpr a) (simplifyLoadStoreExpr b)
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
  | .ite c t f => .ite (simplifyLoadStoreExprR classify c) (simplifyLoadStoreExprR classify t) (simplifyLoadStoreExprR classify f)
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
  | .ite c t f => .ite (canonicalizeExpr c) (canonicalizeExpr t) (canonicalizeExpr f)
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
    | .xmm0 => "xmm0"

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
  | .ite c t f => s!"(ite (not (= {SymExpr.toSMTLib c} (_ bv0 64))) {SymExpr.toSMTLib t} {SymExpr.toSMTLib f})"
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

/-- Does this expression already produce a 32-bit-masked (zero-extended) result in SMT?
    If so, wrapping it in another (zero_extend 32)(extract 31 0) is redundant. -/
def SymExpr.is32Masked {Reg : Type} : SymExpr Reg → Bool
  | .low32 _ | .uext32 _ | .sext8to32 _
  | .sub32 _ _ | .and32 _ _ | .or32 _ _ | .xor32 _ _
  | .shl32 _ _ | .mul32 _ _ | .not32 _ | .sar32 _ _ => true
  | _ => false

mutual
/-- Write SymExpr to a Handle as SMT-LIB2 — avoids O(n²) string building. -/
def SymExpr.writeToSMTLib {Reg : Type} [ToString Reg] (h : IO.FS.Handle) : SymExpr Reg → IO Unit
  | .const v => h.putStr s!"(_ bv{v.toNat} 64)"
  | .reg r => h.putStr s!"reg_{toString r}"
  | .low32 e =>
    -- If e already produces a 32-bit-masked result, skip the redundant wrapper
    if SymExpr.is32Masked e then SymExpr.writeToSMTLib h e
    else do h.putStr "((_ zero_extend 32) ((_ extract 31 0) "; SymExpr.writeToSMTLib h e; h.putStr "))"
  | .uext32 e =>
    if SymExpr.is32Masked e then SymExpr.writeToSMTLib h e
    else do h.putStr "((_ zero_extend 32) ((_ extract 31 0) "; SymExpr.writeToSMTLib h e; h.putStr "))"
  | .sext8to32 e => do h.putStr "((_ zero_extend 32) ((_ sign_extend 24) ((_ extract 7 0) "; SymExpr.writeToSMTLib h e; h.putStr ")))";
  | .sext32to64 e => do h.putStr "((_ sign_extend 32) ((_ extract 31 0) "; SymExpr.writeToSMTLib h e; h.putStr "))"
  | .sub32 l r => do h.putStr "((_ zero_extend 32) (bvsub ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .shl32 l r => do h.putStr "((_ zero_extend 32) (bvshl ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .and32 l r => do h.putStr "((_ zero_extend 32) (bvand ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .or32 l r => do h.putStr "((_ zero_extend 32) (bvor ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .xor32 l r => do h.putStr "((_ zero_extend 32) (bvxor ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .add64 l r => do h.putStr "(bvadd "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .sub64 l r => do h.putStr "(bvsub "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .xor64 l r => do h.putStr "(bvxor "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .and64 l r => do h.putStr "(bvand "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .or64 l r => do h.putStr "(bvor "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .shl64 l r => do h.putStr "(bvshl "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .shr64 l r => do h.putStr "(bvlshr "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .mul64 l r => do h.putStr "(bvmul "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .not64 e => do h.putStr "(bvnot "; SymExpr.writeToSMTLib h e; h.putStr ")"
  | .sar64 l r => do h.putStr "(bvashr "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .sar32 l r => do h.putStr "((_ zero_extend 32) (bvashr ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .ite c t f => do h.putStr "(ite (not (= "; SymExpr.writeToSMTLib h c; h.putStr " (_ bv0 64))) "; SymExpr.writeToSMTLib h t; h.putStr " "; SymExpr.writeToSMTLib h f; h.putStr ")"
  | .not32 e => do h.putStr "((_ zero_extend 32) (bvnot ((_ extract 31 0) "; SymExpr.writeToSMTLib h e; h.putStr ")))"
  | .mul32 l r => do h.putStr "((_ zero_extend 32) (bvmul ((_ extract 31 0) "; SymExpr.writeToSMTLib h l; h.putStr ") ((_ extract 31 0) "; SymExpr.writeToSMTLib h r; h.putStr ")))"
  | .load w m addr => do h.putStr s!"(load_{Width.toSMTWidth w} "; SymMem.writeToSMTLib h m; h.putStr " "; SymExpr.writeToSMTLib h addr; h.putStr ")"

def SymMem.writeToSMTLib {Reg : Type} [ToString Reg] (h : IO.FS.Handle) : SymMem Reg → IO Unit
  | .base => h.putStr "base_mem"
  | .store w m addr val => do
    h.putStr s!"(store_{Width.toSMTWidth w} "; SymMem.writeToSMTLib h m; h.putStr " "; SymExpr.writeToSMTLib h addr; h.putStr " "; SymExpr.writeToSMTLib h val; h.putStr ")"
end

/-- Write SymPC to a Handle as SMT-LIB2 — avoids O(n²) string building. -/
def SymPC.writeToSMTLib {Reg : Type} [ToString Reg] (h : IO.FS.Handle) : SymPC Reg → IO Unit
  | .true => h.putStr "true"
  | .eq l r => do h.putStr "(= "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .lt l r => do h.putStr "(bvult "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .le l r => do h.putStr "(bvule "; SymExpr.writeToSMTLib h l; h.putStr " "; SymExpr.writeToSMTLib h r; h.putStr ")"
  | .and φ ψ => do h.putStr "(and "; SymPC.writeToSMTLib h φ; h.putStr " "; SymPC.writeToSMTLib h ψ; h.putStr ")"
  | .not φ => do h.putStr "(not "; SymPC.writeToSMTLib h φ; h.putStr ")"

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
  | .ite c t f, s => SymExpr.collectRegNames f (SymExpr.collectRegNames t (SymExpr.collectRegNames c s))
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
  | .ite c t f => SymExpr.hasLoad c || SymExpr.hasLoad t || SymExpr.hasLoad f
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
  | .ite c t f, s => SymExpr.collectRegsHS f (SymExpr.collectRegsHS t (SymExpr.collectRegsHS c s))
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

