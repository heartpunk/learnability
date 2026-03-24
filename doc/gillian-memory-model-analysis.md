# Gillian Memory Model Parametricity: Analysis and Application to Our System

## 1. Background: What Gillian Is

Gillian is a multi-language platform for compositional symbolic execution,
developed at Imperial College London (Fragoso Santos, Maksimovic, Ayoun,
Gardner). It supports three analysis modes from a single engine:

- **Symbolic testing**: whole-program path exploration
- **Verification**: separation logic specifications for functions
- **Bi-abduction**: automatic specification inference (compositional bug-finding)

The key insight: all three modes share a single parametric symbolic execution
engine. The engine is parametric on the **memory model** of the target
language, meaning the same core handles JavaScript, C, and CHERI by swapping
in different memory model implementations.

### Key Publications

1. *Gillian, Part I* (PLDI 2020) -- Core framework, parametric soundness
2. *Gillian, Part II* (CAV 2021) -- Compositional memory models, JS+C verification
3. *Compositional Symbolic Execution for Correctness and Incorrectness Reasoning* (2024) -- Consume/produce formalization
4. *Compositional Symbolic Execution for the Next 700 Memory Models* (OOPSLA 2025) -- Full formal foundation, mechanized in Rocq

## 2. GIL: The Intermediate Language

GIL is a simple goto language with these commands:

```
Skip                          -- no-op
x := e                        -- variable assignment
x := [alpha](e1, ..., en)     -- action execution (memory interaction)
goto j                        -- unconditional jump
goto [e] j k                  -- conditional branch
x := f(e1, ..., en)           -- procedure call
return / throw / fail         -- control flow termination
PHI(x: e1, e2, ...)           -- SSA phi nodes
```

The critical command is **action execution** `x := [alpha](e1,...,en)`. Actions
are the interface between GIL programs and the memory model. The action set A
is a parameter of GIL -- different target languages define different actions.

### Comparison with VEX IR

| GIL | VEX IR (our system) |
|-----|---------------------|
| `x := e` | `put reg expr`, `wrTmp n expr` |
| `goto [e] j k` | `exit cond target` |
| `x := [alpha](e)` | `load width addr`, `store width addr val` |
| Parametric action set | Fixed load/store + register file |
| Procedures with specs | Basic blocks with bridge theorems |

VEX IR is more concrete than GIL: it has a fixed notion of registers, memory
loads/stores, and temporaries. GIL abstracts all state interaction behind
actions, making it more flexible but requiring more work to instantiate.

## 3. The Memory Model Interface

### 3.1 Concrete Memory Model (CMM)

From the OOPSLA 2025 paper, a concrete memory model is a tuple:

```
CMM = (CMem, Wf, mu_empty, (·))
```

Where:
- `CMem` is the set of concrete memories
- `Wf ⊆ CMem` is a well-formedness predicate
- `mu_empty ∈ CMem` is the empty/identity memory
- `(·) : CMem × CMem ⇀ CMem` is a partial composition operator

**Required property (IProp 1)**: These form a **partial commutative monoid (PCM)**:
- Associativity: `(mu1 · mu2) · mu3 = mu1 · (mu2 · mu3)`
- Commutativity: `mu1 · mu2 = mu2 · mu1`
- Identity: `mu_empty · mu = mu`
- Partiality: composition may be undefined (conflicting resources)

The PCM is the algebraic backbone of separation logic. Two memories can be
composed iff they represent disjoint resources. The separating conjunction
`P * Q` holds when the memory splits into `mu1 · mu2` with `P` holding on
`mu1` and `Q` on `mu2`.

### 3.2 Memory Actions

Concrete memory actions have the signature:

```
mu.alpha(v_vec) ~> o:(mu', v_vec')
```

Where `o ∈ {ok, err, miss}`:
- `ok` = success, returns updated memory and results
- `err` = language-level fault (null deref, out-of-bounds, etc.)
- `miss` = resource not present (key for bi-abduction)

**Frame properties (IProp 2)** -- the crucial requirement:

**OX Frame** (over-approximate): If `(mu · mu_f).alpha(v) ~> o:(mu', v')`,
then there exists `mu'', v'', o'` such that `mu.alpha(v) ~> o':(mu'', v'')`.
Moreover if `o' != miss` then `o' = o` and `v'' = v'` and `mu' = mu'' · mu_f`.

**UX Frame** (under-approximate): If `mu.alpha(v) ~> o:(mu', v')` and
`o != miss` and `mu' · mu_f` is defined, then
`(mu · mu_f).alpha(v) ~> o:(mu' · mu_f, v')`.

These are the local action axioms of separation logic: an action's behavior
on a small memory extends to any larger memory that includes it as a component.

### 3.3 Symbolic Memory Model (SMM)

A symbolic memory model provides:

```
SMM = (SMem, mu_hat_empty, satisfaction, sym_actions)
```

Where:
- `SMem` is the type of symbolic memories
- Satisfaction: `theta, mu |=_Mem mu_hat` -- concrete memory `mu` satisfies
  symbolic memory `mu_hat` under valuation `theta`
- Symbolic actions: `mu_hat.alpha(E_vec) ~> o:(mu_hat', pi', E_vec')`
  -- same as concrete but on symbolic expressions, returning path constraints

### 3.4 The OCaml Interface (Implementation)

In the actual Gillian codebase (`GillianCore/engine/symbolic_semantics/SMemory.ml`),
the SMemory module type requires:

```ocaml
module type S = sig
  type init_data
  type t                                     (* symbolic memory *)
  type err_t

  val execute_action : string -> t -> Gpc.t -> vt list
    -> (t * vt list, err_t) Symex.result      (* action execution *)

  val consume : string -> t -> Gpc.t -> vt list
    -> (t * vt list, err_t) Symex.result      (* resource consumption *)

  val produce : string -> t -> Gpc.t -> vt list
    -> t Symex.t                               (* resource production *)

  val is_overlapping_asrt : string -> bool

  val assertions : ?to_keep:SS.t -> t -> Asrt.t  (* memory -> SL assertions *)

  val get_fixes : err_t -> Asrt.t list           (* error -> fix candidates *)
  val can_fix : err_t -> bool                     (* is error fixable? *)
  val get_recovery_tactic : t -> err_t -> vt Recovery_tactic.t

  val substitution_in_place : ...                 (* apply substitution *)
  val clean_up : ...                              (* garbage collection *)
  val lvars : t -> SS.t                           (* logical variables *)
  val alocs : t -> SS.t                           (* abstract locations *)
  val mem_constraints : t -> Expr.t list          (* memory constraints *)
  ...
end
```

The three key operations are:
- **execute_action**: Run a memory action during symbolic execution
- **consume**: Extract a resource from memory (frame inference)
- **produce**: Insert a resource into memory (specification production)

### 3.5 Consume and Produce

These are the compositional reasoning primitives:

**Consume** `consume(pred_name, mem, params)`:
- Given a core predicate name and parameters, check that the memory contains
  the described resource
- If found, remove it from memory and return the remaining memory + outputs
- If not found, return an error (which may be fixable via bi-abduction)

**Produce** `produce(pred_name, mem, params)`:
- Given a core predicate name and parameters, add the described resource
  to the memory
- Cannot fail (the precondition guarantees the resource is compatible)

Consume is essentially **frame inference**: consuming `P` from memory `P * Q`
yields the frame `Q`. This is how Gillian implements the frame rule of
separation logic automatically.

### 3.6 Core Predicates

Core predicates are the atomic assertions that describe a memory model's
fundamental resources. They are the target-language-specific component.

For the **linear memory model** (simplest):
- `n |-> v` : cell at address `n` contains value `v`
- `n |-> empty` : cell at address `n` has been freed

For the **C block-offset model**:
- `(loc, ofs) |-> [chunk] v` : at block `loc`, offset `ofs`, chunk type
  `chunk` stores value `v`
- `freed(loc)` : block `loc` has been freed
- `bounds(loc, lo, hi)` : block `loc` has valid range `[lo, hi)`
- `zeros(loc, lo, hi)` : range `[lo, hi)` at `loc` is zero-initialized
- `array(loc, ofs, size, chunk, arr)` : array of values

For **JavaScript** (object-based):
- `(loc, prop) |-> v` : object at `loc` has property `prop` with value `v`
- `metadata(loc, m)` : object at `loc` has metadata `m`
- Prototype chain encoded via metadata predicates

## 4. How JS vs C Memory Models Differ

### 4.1 JavaScript: Object-Property Maps

JS memory is a collection of objects. Each object is a location-indexed
property map. The JS SMemory (`JSILSMemory.ml`) uses a symbolic heap
(`SHeap`) mapping abstract locations to symbolic objects. An object is
a map from property names to symbolic values.

Key JS-specific features:
- **Prototype chains**: Encoded as a metadata property linking object to
  its prototype. Property lookup walks the chain.
- **Closures**: Encoded as special objects with scope chain references.
- **Dynamic property names**: Property names are values (strings), not
  statically known offsets.
- **Extensible objects**: Objects can gain new properties at runtime.

The JS memory actions include:
- `getCell(loc, prop)` : read property
- `setCell(loc, prop, val)` : write property
- `deleteObj(loc)` : delete object
- `hasField(loc, prop)` : test property existence
- `getFields(loc)` : enumerate properties

### 4.2 C: Block-Offset Trees

C memory is a collection of blocks, each with a base address and a range of
valid offsets. The C SMemory (`Gillian-C2/.../MonadicSMemory.ml`) uses a map
from location names to `SHeapTree` structures, where each tree represents an
allocated block.

Key C-specific features:
- **Block-offset pointers**: A pointer is `(block_id, offset)`, not a raw address.
- **Byte-level access**: Memory is byte-addressable with alignment constraints.
- **Chunk types**: Reads/writes specify a "chunk" (int8, int32, float64, etc.)
  determining how bytes map to values.
- **Permissions**: Freeable, Writable, Readable, Nonempty -- a lattice
  controlling what operations are allowed.
- **Freed blocks**: A block transitions to `freed` state; any access is UB.
- **Pointer arithmetic**: Adding to a pointer adjusts the offset within a block.

The C memory actions include:
- `load(loc, chunk, ofs)` : read value at offset with given chunk type
- `store(loc, chunk, ofs, val)` : write value
- `alloc(low, high)` : allocate block with range `[low, high)`
- `free(loc, low, high)` : deallocate block
- `drop_perm(loc, low, high, perm)` : restrict permissions
- `weak_valid_pointer(loc, ofs)` : check pointer validity

### 4.3 The Common Abstraction

Both models implement the same `SMemory.S` interface. The difference is
entirely in what the types `t` and `err_t` are, and how the operations
behave. The Gillian engine never looks inside the memory -- it only calls
`execute_action`, `consume`, and `produce`.

The compositional methodology from CAV 2021 provides a recipe for constructing
these models:
1. Define **core predicates** (atomic memory assertions)
2. Define **consumers** (extract resource from memory, yielding frame)
3. Define **producers** (add resource to memory)
4. Define **action executors** (memory read/write/alloc/free)
5. Prove the frame properties (OX/UX)

## 5. Compositional Reasoning via Bi-Abduction

### 5.1 Function Specifications

In Gillian's verification mode, functions have separation logic specs:

```
{Pre} f(x1, ..., xn) {Post}
```

Where Pre and Post are separation logic assertions (pure facts + spatial
predicates connected by separating conjunction `*`).

Example (C, freeing a linked list node):
```
{(p, 0) |-> [ptr] next * (p, 8) |-> [int32] val * bounds(p, 0, 16)}
  free_node(p)
{freed(p)}
```

### 5.2 Frame Rule

The frame rule says: if `{P} C {Q}` then `{P * R} C {Q * R}` for any `R`.
This is what makes reasoning compositional -- a spec proved for "just the
resources C touches" extends to any larger state.

In Gillian, the frame rule is implemented via consume/produce:
1. At function entry, **consume** the precondition from the current state.
   The remaining state is the frame.
2. Execute the function symbolically.
3. At function exit, **produce** the postcondition into the frame.
4. The result is `frame * postcondition`.

### 5.3 Bi-Abduction

Bi-abduction asks: given a current state and a precondition, what's missing?

```
current_state * [anti-frame] |- precondition * [frame]
```

When `consume` fails with a "missing resource" error, Gillian uses
`get_fixes` to determine what resource would make the consumption succeed.
This missing resource becomes the **anti-frame** -- a precondition that
must be added to the calling function's spec. This propagates upward,
building function specifications from the bottom up.

## 6. Connection to Our System

### 6.1 Architecture Mapping

| Gillian | Our System |
|---------|-----------|
| GIL (goto intermediate language) | VEX IR (from Valgrind) |
| Memory model interface | ByteMem + register file |
| Actions (parametric) | load/store/put/get (fixed) |
| Separation logic specs | Bridge theorems (soundness + completeness) |
| Consume/produce | mem_frame tactic + Footprint.Disjoint |
| Bi-abduction | Not yet present |
| Core predicates | ByteMem_read_write_same/ne, Footprint.Disjoint |
| PCM composition | Footprint disjointness (ad hoc, not algebraic) |
| Symbolic memory | SymMem (store chains) |
| Concrete memory | ByteMem (sorted-list-backed total function) |

### 6.2 What We Already Have

Our system already implements the functional equivalent of several Gillian
components, but without the algebraic structure:

**Concrete memory model**: `ByteMem` in `VexSyntax.lean` -- a total function
`UInt64 -> UInt8` with sorted-list backing for decidable equality. Supports
multi-width read/write in little-endian byte order.

**Frame reasoning**: `Footprint.Disjoint` and `ByteMem_read_write_ne` in
`VexSyntax.lean`, plus the `mem_frame` tactic in `MemFrame.lean`. This proves
that reading from an address disjoint from a write's footprint returns the
original value. This is exactly Gillian's OX frame property for load actions.

**Symbolic memory**: `SymMem` in `VexSummary.lean` -- store chains
`store(store(base, addr1, val1), addr2, val2)` with load resolution via
`simplifyLoadStoreMem`.

**Region-based separation**: `classifyAddr`, `RegionTag`, and region-aware
simplification in the dispatch loop pipeline. Stack vs ELF-loaded vs heap
classification enables non-aliasing proofs without full separation logic.

**Bridge theorems**: `lowerBlockSummaries_sound` and
`lowerBlockSummaries_complete` -- the per-block soundness/completeness results
that are analogous to Gillian's verification of individual functions.

### 6.3 What We're Missing

**PCM structure on memory**: ByteMem has no composition operator. We can't
split a ByteMem into `mu1 · mu2` and recombine them. The Footprint-based
reasoning is point-by-point (each read-write pair) rather than structural
(the whole memory decomposes).

**Separation logic assertions**: We have no assertion language for describing
memory resources. Our "assertions" are path conditions (SymPC) that say what
register/memory values satisfy, but not what memory resources are owned.

**Consume/produce**: We have no mechanism to extract a memory resource and
get back the frame. The `mem_frame` tactic peels writes from reads, but
doesn't decompose memory into owned regions.

**Compositional function specs**: Our bridge theorems are per-basic-block, not
per-function. We don't have function-level pre/postconditions that compose
via the frame rule.

**Bi-abduction**: No automatic inference of missing resources.

## 7. Designing ByteMem as a CMRA

### 7.1 Why CMRA (Iris) Rather Than PCM (Gillian)

Gillian uses plain PCMs for its memory composition. Iris uses **CMRAs**
(Cameras: Commutative Monoids with a Refinement/Agreement structure) which
add two capabilities:

1. **Frame-preserving updates**: The ability to change your owned resource
   without invalidating the frame. PCMs are static -- once composed, the
   components are fixed. CMRAs support dynamic updates.

2. **Step-indexed reasoning**: CMRAs can be defined coinductively (via the
   step-indexed approach), enabling reasoning about recursive protocols.

For our system, the key advantage of CMRAs over PCMs is **update capability**.
When a function writes to memory, it updates its owned region. With a PCM,
you'd need to decompose, update, and recompose. With a CMRA, you perform a
frame-preserving update that changes your fragment while preserving all
other fragments.

### 7.2 The ByteMem CMRA Design

Following the Iris Auth/Fragment pattern already sketched in
`notes/aspacemgr-lts-analysis.md`, the ByteMem CMRA should be:

```
ByteMemRA := Auth(FinMap(UInt64, UInt8 × Perm))
```

Where:
- The authoritative element `● M` tracks the full memory state
- Fragment elements `◯ {addr |-> (val, perm)}` represent owned byte ranges
- `Perm` is a permission lattice (at minimum: Writable, Readable, Freed)
- Composition is disjoint union on the address domain

But this is too fine-grained (byte-level fragments). For practical reasoning,
we need **region-level** ownership:

```
ByteMemRA := Auth(FinMap(Region, RegionContents))

Region := (base : UInt64, size : Nat, tag : RegionTag)
RegionTag := Stack | ELFLoaded Nat | Heap
RegionContents := UInt64 -> UInt8   -- the bytes in this region
```

This directly mirrors our existing `classifyAddr` infrastructure:
- Stack regions own `[rsp, rbp]` ranges
- ELF-loaded regions own `.text`, `.data`, `.got`, etc.
- Heap regions own dynamically allocated blocks

### 7.3 Learning from Gillian's C Block-Offset Model

Gillian-C's `SHeapTree` is a per-block memory structure. The overall memory is:

```
Mem = Map(LocationName, SHeapTree)
```

Each `SHeapTree` supports:
- `load(tree, chunk, offset) -> (value, tree')`
- `store(tree, chunk, offset, value) -> tree'`
- `cons_single(tree, offset, chunk) -> (value, perm, tree')` (consume)
- `prod_single(tree, offset, chunk, value, perm) -> tree'` (produce)
- `alloc(low, high) -> tree`
- `free(tree, low, high) -> tree'`
- `cons_bounds(tree) -> (range, tree')` (consume bounds info)

The key insight: the tree tracks both **content** (what bytes are stored) and
**permission** (what operations are allowed). Consumption extracts a value
and its permission; production inserts both.

For our ByteMem CMRA, the analog is:

```
-- Per-region "heap tree" for our system
structure RegionMem where
  bytes : UInt64 -> UInt8            -- content
  perm : Perm                        -- region-level permission
  bounds : UInt64 × UInt64           -- valid range [lo, hi)

-- Consume: extract value from region, get remaining region
consume_cell (r : RegionMem) (addr : UInt64) (w : Width) :
  Option (UInt64 × RegionMem)        -- (value, remaining)

-- Produce: insert value into region
produce_cell (r : RegionMem) (addr : UInt64) (w : Width) (v : UInt64) :
  Option RegionMem
```

### 7.4 Connecting to Our Existing Infrastructure

Our `Footprint.Disjoint` already captures the core of the frame property:

```lean
theorem ByteMem_read_write_of_disjoint (lw sw : Width) (M : ByteMem)
    (a v b : UInt64)
    (h : Footprint.Disjoint (Footprint.ofWidth a sw) (Footprint.ofWidth b lw)) :
    ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b
```

This IS Gillian's OX frame property, specialized:
- The "action" is `write sw a v`
- The "frame" is the read at address `b`
- Footprint disjointness is the condition for composability
- The read result is unchanged (frame preservation)

The gap is that we prove this theorem per-footprint-pair rather than
structurally. A CMRA-based approach would instead:
1. Decompose `M = M_write * M_frame` where `M_write` owns the write region
2. Execute the write on `M_write`, getting `M_write'`
3. Recompose: `M' = M_write' * M_frame`
4. The read on `M_frame` is unchanged by construction

### 7.5 The SymMem Store Chain as a Gillian-Style Symbolic Memory

Our `SymMem` type already has the same structure as Gillian's symbolic memory
for a linear model:

```lean
inductive SymMem (Reg : Type) where
  | base                                                    -- empty/initial
  | store : Width -> SymMem Reg -> SymExpr Reg -> SymExpr Reg -> SymMem Reg
```

Gillian's linear symbolic memory is `LExp ->_fin (LExp | freed)`. Our
SymMem is a store chain, which is the **log-structured** representation of
the same thing. Each `store` records a write; `simplifyLoadStoreMem`
resolves loads by walking the chain and checking address (non-)equality.

The `resolveLoadFrom` function with region-aware classification is our
analog of Gillian's `execute_action` for loads: it walks the store chain,
using region tags to skip provably non-aliasing stores.

### 7.6 Staged Plan

**Stage 1** (now): Continue using Footprint-based reasoning. The `mem_frame`
tactic plus region classification is sufficient for per-block proofs.

**Stage 2**: Define a `MemRegion` type and a decomposition of ByteMem into
regions. Prove that ByteMem can be split along region boundaries and
recombined. This gives us a PCM without needing full Iris.

```lean
structure MemRegion where
  base : UInt64
  size : Nat
  bytes : Fin size -> UInt8

def ByteMem.decompose (m : ByteMem) (regions : List MemRegion) :
  Prop := -- m is the union of the regions, and they don't overlap

theorem ByteMem.frame_write (m : ByteMem) (r1 r2 : MemRegion)
    (h_decomp : m.decompose [r1, r2])
    (h_in_r1 : footprint_in_region write_fp r1) :
    (m.write w a v).decompose [r1.write w a v, r2]
```

**Stage 3**: Lift to an Iris CMRA. The `MemRegion` PCM becomes the underlying
monoid of an Auth CMRA. Fragment ownership `own gamma (frag {region_i})`
enables per-function reasoning: a function that only touches stack memory
holds a fragment for the stack region, and its proof is independent of what
happens in other regions.

**Stage 4**: Bridge theorem composition via the frame rule. Given:
- Block A's bridge theorem: `{stack_pre_A} block_A {stack_post_A}`
- Block B's bridge theorem: `{stack_pre_B} block_B {stack_post_B}`
- Frame: `elf_mem * heap_mem` (unchanged by either block)

Compose: `{stack_pre_A * elf_mem * heap_mem} A;B {stack_post_B * elf_mem * heap_mem}`

This is exactly how Gillian composes function specs: consume preconditions,
produce postconditions, and the frame flows through automatically.

## 8. Key Lessons from Gillian

### 8.1 Actions Are the Right Abstraction Boundary

Gillian's most important design decision: the memory model is accessed ONLY
through named actions with typed parameters and results. The engine never
looks at memory internals.

We partially have this: VEX IR `load` and `store` statements are our actions.
But our proofs currently look inside ByteMem (the `mem_frame` tactic walks
the internal structure). Moving toward opaque memory with action-level
specifications would make proofs more modular.

### 8.2 Consume/Produce Enables Verification AND Testing

Gillian's `consume` and `produce` serve triple duty:
- In verification: implement the frame rule
- In testing: check assertions against concrete states
- In bi-abduction: identify missing resources

For our system, if we defined consume/produce for ByteMem regions, we could:
- Frame-off untouched memory during block proofs (cleaner bridge theorems)
- Check postconditions against test executions (validation)
- Eventually infer what memory a function needs (automatic spec inference)

### 8.3 The Miss/Error/OK Trichotomy

Gillian distinguishes three outcomes for memory actions:
- `ok`: success
- `err`: language-level fault (real bug)
- `miss`: resource not present (insufficient info, not necessarily a bug)

This trichotomy enables bi-abduction: a `miss` triggers inference of
additional preconditions rather than failure. Our current system treats
all failures uniformly. Distinguishing "this memory access would fault"
from "I don't know what's at this address" would improve our analysis.

### 8.4 Region Classification IS Separation

Our region-based address classification (`classifyAddr` returning `RegionTag`)
is doing exactly what Gillian's PCM composition checks: "are these two
resources disjoint?" Gillian phrases it algebraically (mu1 · mu2 is defined
iff disjoint); we phrase it semantically (addresses in different regions
can't alias). The substance is identical.

The path from our current approach to full separation logic is:
1. (Done) Region tags + non-aliasing
2. (Next) Region-level memory decomposition
3. (Future) Auth/Fragment CMRA with Iris

### 8.5 Symbolic Memory Should Be Log-Structured with Lazy Resolution

Both Gillian and our system use a log-structured symbolic memory: writes
are recorded as a chain, reads walk the chain. This is the right choice for
symbolic execution because:
- No eagerly-computed normal form needed
- Reads resolve lazily (only when the value is actually needed)
- Region classification prunes the chain during resolution
- The chain naturally records the execution history

Our `simplifyLoadStoreMem` with region-aware `resolveLoadFrom` is
architecturally equivalent to Gillian's symbolic memory action executor.

## 9. Specific Recommendations

### 9.1 Near-Term (No Iris Required)

1. **Formalize the region decomposition**: Define `MemRegion` and prove that
   `ByteMem` decomposes into non-overlapping regions. This is the PCM.

2. **Define action-level specs for load/store**: State the frame properties
   at the action level rather than the byte level:
   ```lean
   theorem load_frame (m : ByteMem) (r1 r2 : MemRegion)
       (h : m.decompose [r1, r2]) (h_in : addr_in_region load_addr r2) :
       ByteMem.read w m addr = ByteMem.read w r2.to_mem addr
   ```

3. **Per-function bridge theorems with explicit frames**: Instead of proving
   bridge theorems for the whole state, prove them relative to a frame:
   ```lean
   theorem block_bridge (pre post frame : MemRegion)
       (h_pre : stack_satisfies pre) :
       execBlock block (combine pre frame) = combine post frame
   ```

### 9.2 Medium-Term (Toward Iris)

4. **Define the ByteMem CMRA**: Following the Auth/Fragment pattern from
   `notes/aspacemgr-lts-analysis.md`, build the CMRA over FinMap(Region, Contents).

5. **Port the frame rule**: Prove that function-level bridge theorems compose
   via the frame rule, using CMRA fragment ownership.

6. **Consume/produce for SymMem**: Define symbolic consume/produce that
   extract/insert region-level resources from SymMem store chains.

### 9.3 Long-Term (Full Compositional Verification)

7. **Bi-abduction**: When analyzing a function, automatically infer what
   memory regions it needs (the anti-frame) by tracking which loads fail
   with "miss" rather than "err".

8. **Cross-function composition**: Compose per-function specs into whole-program
   proofs using the frame rule, analogous to how Gillian composes function
   specifications.

## 10. Summary

Gillian demonstrates that parametric memory models work at scale for real
languages (JS, C, CHERI). The key abstraction is:

> **A memory model is a PCM with actions that satisfy frame properties,
> plus consume/produce operations for compositional reasoning.**

Our system already has the functional pieces:
- ByteMem with read-write frame reasoning (Footprint.Disjoint)
- Region classification for non-aliasing (classifyAddr)
- Symbolic store chains with lazy load resolution (SymMem)
- Per-block bridge theorems (soundness + completeness)

What's needed is the algebraic structure to connect them:
- Region-level PCM decomposition of ByteMem
- Action-level frame properties (upgrade from byte-level)
- Consume/produce for compositional function specs
- Eventually, an Iris CMRA for full separation logic reasoning

The staged plan (Footprint -> PCM -> CMRA) is the natural path. Each stage
provides independent value and the transitions are incremental.
