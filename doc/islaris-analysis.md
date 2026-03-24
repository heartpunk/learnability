# Islaris Analysis: Lessons for the Learnability System

## Date: 2026-03-23

## What Islaris Is

Islaris (Sammler et al., PLDI 2022) is the first system to verify machine code against
*authoritative* ISA semantics -- the official Sail models for Armv8-A and RISC-V, not
hand-written abstractions. It combines two engines:

1. **Isla**: a Rust-based symbolic execution engine that evaluates Sail ISA specifications
   using an SMT solver, producing simplified *traces* of instruction effects.
2. **Iris**: a higher-order separation logic framework in Coq, on top of which Islaris
   defines a program logic for reasoning about those traces.

The key architectural insight is *separation of concerns*: Isla handles the inherent
complexity of ISA specifications (the Sail model for `ldrb` alone is 2000+ lines across
dozens of functions), while Iris handles the reasoning about program correctness. The
interface between them is the *Isla trace* -- a simplified record of register reads/writes
and memory loads/stores that Isla extracts from the full ISA specification.

## Architecture: The Pipeline

```
Machine code (objdump)
    |
    v
Islaris frontend (annotated assembly + constraints)
    |
    v
Isla (symbolic execution of Sail ISA spec + SMT solver)
    |
    v
Isla traces (deep-embedded in Coq, one per instruction)
    |
    v
Islaris separation logic (wp over traces, Lithium automation)
    |
    v
Verified specification (safety + trace specification, machine-checked in Coq)
```

### Isla Traces

An Isla trace is an inductive datatype in Coq with three constructors:

- **tnil**: empty trace (instruction complete)
- **tcons**: a single event (register read/write, memory load/store, assertion, branch)
  followed by a continuation trace
- **tcases**: nondeterministic choice among multiple sub-traces (for conditional branches
  within the ISA spec itself -- e.g., whether an address translation hits a TLB entry)

Events carry labels encoding:
- Register operations: read/write with accessor paths (for structured registers like
  `mstatus` which have named bit-fields)
- Memory operations: load/store with addresses and data as bitvectors
- Control flow: branch targets, taken/not-taken
- Assertions and assumptions about machine state (from SMT constraints)

The trace is the *residual* of symbolic execution: Isla has already pruned unreachable
paths using the SMT solver, so the trace only contains feasible instruction behaviors.
For a simple `add x0, x1, #3`, the trace is compact: read x1, compute addition, write x0.
For a memory instruction like `ldrb`, it encodes address translation, permission checks,
alignment checks, and the actual load -- but only the feasible paths after SMT pruning.

### How Isla Connects to Iris

The connection happens through the `isla_lang` construction: Isla traces are registered as
an Iris `Language`, with:
- **Expression**: the remaining trace (`isla_trace`)
- **State**: a pair of `(seq_local_state, seq_global_state)` where local state is
  registers + PC, global state is the instruction map + memory map
- **Step relation**: `trace_step` advances the trace by one event, updating registers/memory

This lets Iris's generic weakest-precondition machinery (`WP`) work directly over traces.
The `WPasm` predicate is the main proof obligation: given the current trace and machine
state resources, prove the specification holds after execution.

## Machine State as Iris Resources

This is where Islaris makes its most interesting design choices, and where the comparison
to our system is most instructive.

### Ghost State / Resource Algebras

Islaris defines several resource algebras (CMRAs) in `ghost_state.v`:

**Instruction table** (`instrtblUR`): An `agreeR` over a gmap from addresses to traces.
This is *persistent* -- once established, any thread can look up what instruction lives at
a given address. This models the code segment as immutable.

**Memory** (`heap_mem_name`): A ghost map from 64-bit addresses to 8-bit values (bytes).
Memory ownership is *fractional* -- `a ↦ₘ{q} v` means you own fraction `q` of byte at
address `a` with value `v`. Full ownership (`q = 1`) is needed to write; any fraction
suffices to read.

**Registers** (`heap_regs_name`): A ghost map from register names to bitvector values.
`r ↦ᵣ{q} v` means fractional ownership of register `r` with value `v`. Registers also
support structured access -- `struct_reg_mapsto` handles fields within registers like
`mstatus.MPP`.

**Backed memory** (`backed_memUR`): An `agreeR` over the set of addresses that are backed
by actual memory (vs. MMIO regions). This lets Islaris distinguish RAM from memory-mapped
I/O.

### Memory Predicates

The key predicates, from simplest to most complex:

1. **`mem_mapsto_byte a q v`**: Fractional ownership of a single byte at address `a`.
   The fundamental building block.

2. **`a ↦ₘ{q} v` (mem_mapsto)**: Ownership of a multi-byte word at address `a`,
   *decomposed to byte-level ownership* via `bv_to_little_endian`. An 8-byte value at
   address `a` becomes 8 individual byte ownerships at `a`, `a+1`, ..., `a+7`.

3. **`mem_mapsto_array a n`**: Array of `n` words, element-wise decomposition.

4. **`a ↦ₘ? n` (mem_mapsto_uninit)**: Existentially quantified -- `n` bytes at address `a`
   with unknown values. Used for uninitialized regions.

5. **`mmio_range a l`**: Asserts addresses in `[a, a+l)` are NOT in the backed memory set,
   modeling memory-mapped I/O.

### How the Frame Rule Works

This is the critical mechanism. In separation logic, the frame rule says:

```
{P} c {Q}  implies  {P * R} c {Q * R}
```

For machine memory, this means: if you prove a store to address `a` updates `a ↦ₘ v` to
`a ↦ₘ v'`, then any memory at non-overlapping addresses is automatically preserved.

Islaris achieves this through Iris's generic ghost state mechanism:
- Memory is a ghost map: each byte has its own ghost cell
- A store to address `a` only touches the ghost cells for `a` through `a+width-1`
- Ghost cells at other addresses are untouched -- they survive in the frame automatically
- Non-aliasing is STRUCTURAL: if you hold `a ↦ₘ v` and `b ↦ₘ w` separately (with `*`),
  then `a` and `b` are automatically disjoint (the separating conjunction enforces it)

### Lifting Lemmas

The connection between traces and resources happens through lifting lemmas:

- **`wp_read_reg r v Q`**: If you own `r ↦ᵣ v`, a register read produces value `v` and
  continues with `Q v`. Register ownership is returned unchanged.

- **`wp_write_reg r v v' Q`**: If you own `r ↦ᵣ v`, a register write updates it to
  `r ↦ᵣ v'` and continues with `Q`.

- **`wp_read_mem a v Q`**: If you own the bytes at `a`, a memory load produces the
  reconstructed value and returns ownership.

- **`wp_write_mem a v v' Q`**: Memory store consumes full ownership of the old value
  and produces ownership of the new value.

- **`wp_next_instr pc t Q`**: If the instruction table maps `pc` to trace `t`, executing
  the next instruction reduces to proving `Q` for trace `t`.

### Address Arithmetic

Islaris handles address arithmetic through a combination of:

1. **Bitvector normalization**: `normalize_instr_addr` wraps addresses modulo 2^64;
   `normalize_bv_wrap` handles bitvector constants.

2. **SMT-backed simplification**: Since Isla uses Z3/CVC5 during trace generation, many
   address constraints are already simplified before reaching Coq.

3. **Coq-level automation**: `bitblast`, `lia`, and custom rewriting handle remaining
   arithmetic in proofs.

## Automation: Lithium

Lithium is an automated separation logic programming language originally designed for
RefinedC (Sammler's earlier work on verifying C code). Islaris adapts it.

Key automation components:

1. **Register collection management** (`regcol_*`): Efficient tracking of which registers
   you own. `regcol_lookup` finds a register, `regcol_extract` removes it from a collection,
   `regcol_cancel` computes the difference between hypothesis and goal register sets.

2. **Subsumption rules**: Type class instances that automatically discharge frame reasoning.
   `subsume_reg` for single registers, `subsume_regcol_regcol` for comparing register
   collections.

3. **Expression computation** (`compute_wp_exp`): Evaluates ISA expressions at proof time,
   avoiding runtime computation overhead.

4. **Instruction handling** (`FindInstrKind`): Dispatches between concrete instruction
   traces, predicate-based preconditions, and trap scenarios.

The automation uses the separation logic context to guide proof search -- this is what
makes it practical despite the complexity of full ISA semantics.

### SMT in Proofs

Isla uses SMT (Z3) *during trace generation*, not during Coq proof checking. This is a
deliberate trust boundary decision: the SMT solver simplifies the ISA specification into
a manageable trace, then all reasoning about that trace is done in Coq with
machine-checked proofs. The SMT solver is trusted for trace generation but not for
correctness arguments.

## The Adequacy Theorem

The top-level soundness result:

```coq
Lemma isla_adequacy Σ `{!islaPreG Σ}
  (instrs : gmap addr isla_trace) (mem : mem_map)
  (regs : list reg_map) (Pκs : spec) t2 σ2 κs n:
  Pκs [] →
  (∀ {HG : islaG Σ},
   ⊢ instr_table instrs -∗ backed_mem (dom mem) -∗ spec_trace Pκs -∗
     ([∗ map] a↦b∈mem, bv_unsigned a ↦ₘ b)
   ={⊤}=∗ [∗ list] rs ∈ regs, ∀ (_ : threadG),
     ([∗ map] r↦v∈rs, r ↦ᵣ v) -∗ WPasm tnil) →
  nsteps n (initial_local_state <$> regs,
    {| seq_instrs := instrs; seq_mem := mem |}) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs.
```

This says: if you can prove the separation logic assertions (instruction table, memory
ownership, register ownership) imply `WPasm tnil` (the weakest precondition for completed
execution), then:
1. The machine never gets stuck (safety)
2. The execution trace satisfies the specification `Pκs` (correctness)

## How Our System Differs

### Fundamental Orientation

| Dimension | Islaris | Learnability |
|-----------|---------|-------------|
| **Goal** | Verify code meets a spec | Extract a spec from code |
| **Direction** | Spec -> proof of code | Code -> extracted model |
| **Logic** | Hoare-style (pre/postcondition) | Bisimulation (behavioral equivalence) |
| **ISA source** | Sail (authoritative formal models) | pyvex/VEX IR (Valgrind's lifter) |
| **Scope** | Individual functions | Whole-program dispatch loops |
| **Scale** | Handful of case studies | 13 subjects, automated pipeline |

### ISA Semantics Source

Islaris uses Sail, the authoritative ISA specification language. The Armv8-A Sail model
is auto-translated from ARM's internal ASL definitions. The RISC-V Sail model is the
official formal model. These are comprehensive: every instruction behavior, every
exception, every address translation mode.

We use pyvex, Valgrind's VEX IR lifter. pyvex translates x86-64 instructions into VEX IR
statements (Put, Get, Store, Load, conditional exits). This is a lossy translation -- VEX
abstracts away some ISA details (segment registers, precise flag semantics for unusual
flag combinations, etc.). Our `docs/graduated-semantics.md` identifies this as the Level 4
trust boundary: all our results are conditional on pyvex faithfully lifting x86-64 to VEX.

**Lesson**: Islaris's architecture shows that the Isla trace abstraction -- reducing
thousands of lines of ISA spec to a compact event sequence -- is exactly what makes
verification tractable. Our VEX IR plays an analogous role: it *is* a trace of instruction
effects, just produced by a less trustworthy source. If we ever move to Sail-based ISA
specs (as mentioned in `graduated-semantics.md`), the Isla architecture is the template
for how to integrate them.

### Memory Model

**Islaris**: Memory is a ghost map from addresses to bytes, with *fractional ownership*
enforced by Iris's separation logic. Non-aliasing is structural -- holding `a ↦ₘ v * b ↦ₘ w`
implies `a ≠ b` by the semantics of `*`.

**Learnability**: Memory is `ByteMem`, a total function `UInt64 → UInt8` with a sorted-list
backing for decidable equality. Non-aliasing is proved by `Footprint.Disjoint`, which
checks all byte-pair inequalities. The `mem_frame` tactic automates this with three
strategies: `native_decide` for concrete addresses, `Disjoint_add_left` for same-base
addresses, and `interval_cases` for symbolic stack-vs-data addresses.

**Key difference**: Islaris gets non-aliasing "for free" from separation logic's `*`
connective. We have to prove it explicitly for each read-after-write pattern. This is
because we use a functional memory model (total functions) rather than a resource-based
one. The functional model gives us decidable equality (important for our pipeline) but
requires explicit frame reasoning.

**Lesson**: Our `Footprint.Disjoint` + `mem_frame` tactic is essentially a decision
procedure for a fragment of separation logic's frame rule. We're reimplementing part of
what Iris gives you structurally. This is the right trade-off for now (we need `DecidableEq`
on states, which separation logic resources don't give you), but it's worth understanding
that we're in the same conceptual space.

### Automation Philosophy

**Islaris**: Lithium provides a general separation logic programming language. Register
collections are managed as first-class objects with lookup/extract/cancel operations.
Subsumption is handled by type class resolution. This is heavy infrastructure but handles
complex patterns (structured register fields, MMIO ranges, etc.) uniformly.

**Learnability**: The `mem_frame` tactic is a targeted decision procedure for the specific
pattern `ByteMem.read w (ByteMem.write w' M a v) b` where the read and write footprints
don't overlap. It walks the expression tree, collects read-of-write patterns, scores them
by complexity (addresses without memory loads first), and peels writes one at a time.
For registers, we use `simp` with `ConcreteState.read`/`ConcreteState.write` lemmas.

**Lesson**: Our approach is more ad hoc but also more targeted. The `mem_frame` tactic
solves our specific problem efficiently. As we scale to more complex programs (multiple
function calls, heap allocation, aliased pointers), we may need to move toward something
more like Lithium's general framework. The "priority-ordered peeling" strategy in
`mem_frame` is actually a good foundation -- it's doing the same work as Lithium's
subsumption rules, just in a more imperative style.

### What They Prove vs What We Prove

**Islaris**: For each function, proves `{P} code {Q}` -- given precondition P on machine
state, the code establishes postcondition Q. Specifications are hand-written. The key
theorem is adequacy: Iris proofs imply actual machine safety + trace specification.

**Learnability**: For the dispatch loop of a program, proves bisimulation between the
extracted LTS and the concrete system. The specification (the LTS) is *computed*, not
hand-written. The key theorems are `extraction_exists` (iterative refinement converges)
and the pipeline bridge (`pipeline_extracted_model_adequate`).

**Lesson**: These are complementary, not competing. Islaris proves a given spec is correct.
We *discover* the spec. In principle, you could use Islaris to verify that our extracted
model is correct -- the extracted LTS gives you the pre/postconditions, and Islaris could
verify them against the authoritative ISA semantics. This would replace pyvex as the trust
boundary.

## What We Can Learn

### 1. Trace Abstraction is the Right Interface

Islaris's most important insight for us is that the *trace* -- a sequence of register
reads/writes and memory loads/stores -- is the right abstraction boundary between ISA
complexity and verification reasoning. Our VEX IR blocks are already traces in this sense.
The key architectural lesson is to keep the trace abstraction clean and narrow, then build
all reasoning on top of it.

Our `Block` structure (`stmts : List (Stmt Reg)`, `ip_reg`, `next`) is structurally
analogous to an Isla trace: a sequence of effects (register puts, memory stores, loads)
with a next-instruction-pointer. The main difference is that our traces come from pyvex
rather than from symbolic execution of Sail.

### 2. Byte-Level Decomposition for Memory

Islaris decomposes multi-byte values into byte-level ownership. Our `ByteMem` does
the same thing functionally: `ByteMem.write64le` breaks a 64-bit value into 8 byte
writes; `ByteMem.read64le` reconstructs from 8 byte reads. The `readLEAux`/`writeLEAux`
functions implement little-endian decomposition.

The lesson is that byte-level decomposition is unavoidable for real ISA reasoning -- mixed
widths (a 32-bit write followed by an 8-bit read of one of those bytes) require reasoning
at the byte level. Both systems handle this, just with different mechanisms (ghost state
vs. functional model).

### 3. Address Arithmetic Strategies

Both systems face the same address arithmetic challenge and use similar strategies:

| Strategy | Islaris | Learnability |
|----------|---------|-------------|
| Concrete addresses | SMT during trace gen | `native_decide` |
| Same-base symbolic | Rewriting + lia | `Disjoint_add_left` + `native_decide` |
| Cross-region | Bounds from preconditions | `interval_cases` via `StackSeparation` |
| Bitvector reasoning | `bitblast` | `bv_decide`, `bv_omega` |

Our three-strategy cascade in `mem_frame` mirrors Islaris's approach but in a more
targeted form. The key insight from Islaris is that *most* address arithmetic falls
into simple patterns (concrete, same-base) that can be decided cheaply, with expensive
reasoning reserved for the hard cases.

### 4. Potential Future Architecture: Islaris-Backed Certification

The most ambitious takeaway is a potential future architecture:

```
Binary
  |
  v
pyvex -> VEX IR -> Symbolic execution -> Extracted LTS (our current pipeline)
  |
  v
Cross-check: for each instruction in the LTS,
use Isla + Sail to verify the VEX IR is faithful to the ISA
  |
  v
Isla-certified trace -> Islaris separation logic proof
  |
  v
End-to-end certified bisimulation (no pyvex trust boundary)
```

This would replace the Level 4 trust boundary (pyvex fidelity) with a mechanically
verified check. Each VEX IR instruction summary would be verified against the Sail ISA
model. Isla already supports generating "simplified semantics summaries" for concrete
opcodes, which is exactly what we would need.

The engineering challenge is substantial -- we would need to integrate Isla (Rust) with
our Lean pipeline, and map VEX IR statements to Sail instruction effects. But the
architectural path exists.

### 5. What We Do That Islaris Cannot

It's worth noting where our approach has advantages:

- **Scale**: Islaris verifies individual functions with hand-written specs. We extract
  models from 13 subjects automatically. The dispatch loop analysis, branch composition,
  and convergence checking are not things Islaris addresses.

- **Discovery**: Islaris requires a human to write the specification. We compute it.
  The extracted LTS *is* the specification, discovered by iterative refinement.

- **Decidable equality**: Our functional memory model gives us `DecidableEq` on states,
  which is essential for the convergence/fixpoint machinery. Iris resources don't have
  decidable equality -- they're propositions in a higher-order logic.

- **Bisimulation vs Hoare triples**: Our target (behavioral equivalence) is a different
  kind of correctness than Islaris's (specification conformance). Bisimulation captures
  "the model behaves exactly like the system" rather than "the system satisfies these
  properties."

## References

- Sammler, Hammond, Lepigre, Campbell, Pichon-Pharabod, Dreyer, Garg, Sewell.
  "Islaris: Verification of Machine Code Against Authoritative ISA Semantics."
  PLDI 2022. https://dl.acm.org/doi/10.1145/3519939.3523434
  PDF: https://www.cl.cam.ac.uk/~pes20/2022-pldi-islaris.pdf
- Islaris source: https://github.com/rems-project/islaris
- Isla source: https://github.com/rems-project/isla
- Sammler thesis: https://plv.mpi-sws.org/sammler-thesis/thesis-screen.pdf
- Isla paper: Armstrong et al. "Isla: Integrating Full-Scale ISA Semantics and
  Axiomatic Concurrency Models." CAV 2021.
  https://link.springer.com/chapter/10.1007/978-3-030-81685-8_14
- Artifact: https://zenodo.org/records/6417959
