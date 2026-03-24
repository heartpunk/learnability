# Valgrind aspacemgr as a Labeled Transition System

## 1. The aspacemgr: What It Is

Valgrind's address space manager (`coregrind/m_aspacemgr/`) maintains a
software model of the entire virtual address space of the process under
instrumentation. It is, in essence, a sorted interval map: an array of
`NSegment` records that partition `[0, Addr_MAX]` into contiguous,
non-overlapping regions. Every byte of the address space belongs to exactly
one segment. The kernel is the actual authority on mappings, but aspacemgr
tracks an authoritative *model* that it keeps consistent with the kernel via
an advise-then-notify protocol.

### 1.1 The State: NSegment Array

The state is declared in `aspacemgr-linux.c:297`:

```c
static NSegment nsegments[VG_N_SEGMENTS];  // up to 30000 entries
static Int      nsegments_used = 0;
```

Each `NSegment` (defined in `pub_tool_aspacemgr.h:92-118`) carries:

| Field     | Type       | Meaning |
|-----------|------------|---------|
| `kind`    | `SegKind`  | One of 7 mutually-exclusive kinds (one-hot encoded) |
| `start`   | `Addr`     | Lowest address (page-aligned) |
| `end`     | `Addr`     | Highest address (end+1 page-aligned) |
| `smode`   | `ShrinkMode` | How a reservation can be resized |
| `dev`, `ino`, `offset`, `mode`, `fnIdx` | file metadata | For SkFile{C,V} only |
| `hasR`, `hasW`, `hasX` | `Bool` | Permission bits |
| `hasT`    | `Bool`     | Translations taken from this region |
| `isCH`    | `Bool`     | Is client heap (SkAnonC only) |

### 1.2 The Seven Segment Kinds

```
SkFree   (0x01)  -- unmapped space, available for allocation
SkAnonC  (0x02)  -- anonymous mapping, client-owned
SkAnonV  (0x04)  -- anonymous mapping, valgrind-owned
SkFileC  (0x08)  -- file mapping, client-owned
SkFileV  (0x10)  -- file mapping, valgrind-owned
SkShmC   (0x20)  -- shared memory, client-owned
SkResvn  (0x40)  -- reservation (growth space for stack/brk)
```

The one-hot encoding permits bitwise OR for kind-masks in queries like
`VG_(am_get_segment_starts)`.

The ownership distinction (C vs V) is fundamental: Valgrind interposes on
the client's address space management but must also allocate its own memory
(shadow memory, translation cache, tool state). The two namespaces must not
collide.

### 1.3 The Invariants

`preen_nsegments()` (line 723) enforces the representation invariants on
every mutation:

**INV-1: Full coverage.**
`nsegments[0].start == Addr_MIN` and `nsegments[nsegments_used-1].end == Addr_MAX`.
Every byte of the address space is accounted for.

**INV-2: Contiguity (no gaps, no overlaps).**
For all `i` in `[1, nsegments_used)`: `nsegments[i-1].end + 1 == nsegments[i].start`.

**INV-3: Per-segment well-formedness** (`sane_NSegment`, line 611):
- `start <= end`, both page-aligned.
- SkFree: no permissions, no file metadata, `smode == SmFixed`.
- SkAnon{C,V}/SkShmC: `smode == SmFixed`, no file metadata.
- SkFile{C,V}: `smode == SmFixed`, valid filename index.
- SkResvn: no permissions, no file metadata (but smode may vary).
- `isCH` only on SkAnonC; `hasT` only on client segments.

**INV-4: Normalization (maximally merged).**
Adjacent segments with identical kind and compatible metadata are merged
(`maybe_merge_nsegments`, line 662). This ensures a canonical representation.

**INV-5: Kernel consistency (runtime check, not structural).**
`sync_check_mapping_callback` reads `/proc/self/maps` and verifies agreement.
At `--sanity-level=3` this runs before and after every syscall.

### 1.4 The Operations (Transitions)

The aspacemgr exposes two classes of operations:

**Notify operations** (recording what the kernel did):
- `VG_(am_notify_client_mmap)(addr, len, prot, flags, fd, offset)` -- record a successful client mmap
- `VG_(am_notify_client_shmat)(addr, len, prot)` -- record a successful shmat
- `VG_(am_notify_mprotect)(start, len, prot)` -- record a successful mprotect
- `VG_(am_notify_munmap)(start, len)` -- record a successful munmap

**Combined advise+execute+notify operations** (Valgrind-initiated):
- `VG_(am_mmap_anon_fixed_client)(start, length, prot)`
- `VG_(am_mmap_anon_float_client)(length, prot)`
- `VG_(am_mmap_anon_float_valgrind)(length)`
- `VG_(am_mmap_file_fixed_client)(start, length, prot, fd, offset)`
- `VG_(am_extend_into_adjacent_reservation_client)(addr, delta)`
- `VG_(am_extend_map_client)(addr, delta)` (mremap support)
- `VG_(am_munmap_client)(start, length)`
- `VG_(am_munmap_valgrind)(start, length)`

All operations funnel through `add_segment()` (line 1468) which:
1. Validates the new segment (`sane_NSegment`).
2. Splits existing segments at the new segment's boundaries (`split_nsegments_lo_and_hi`).
3. Replaces the spanned segment range with the new segment.
4. Re-preens (merges adjacent compatible segments).

This is the core transition mechanism. Every mutation to the segment array
goes through `add_segment` followed by `preen_nsegments`.

---

## 2. Formalizing as an LTS

### 2.1 The State Space

```
State := { segs : Array NSegment //
           sorted segs ∧ non_overlapping segs ∧ full_coverage segs ∧
           ∀ s ∈ segs, well_formed s ∧ normalized segs }
```

More precisely, a state is a *finite partition* of `[0, 2^64 - 1]` into
contiguous intervals, each labeled with a segment kind and metadata. This is
isomorphic to a function `Addr → SegmentInfo` that is piecewise-constant
and changes only at page boundaries, but the array representation makes the
finiteness and sortedness structural.

In Lean terms, following the project's existing `LTS` structure:

```lean
structure AspacemState where
  segs : List NSegment
  sorted : List.Sorted (· < ·) (segs.map (·.start))
  contiguous : ∀ i, i + 1 < segs.length →
    (segs[i]!).end + 1 = (segs[i+1]!).start
  full_lo : segs.head?.map (·.start) = some 0
  full_hi : segs.getLast?.map (·.end) = some Addr_MAX
  well_formed : ∀ s ∈ segs, sane_NSegment s
```

### 2.2 The Labels (Actions)

```
inductive AspacemLabel where
  | mmap_anon   : Addr → Size → Prot → Owner → AspacemLabel
  | mmap_file   : Addr → Size → Prot → Owner → FileInfo → AspacemLabel
  | munmap      : Addr → Size → AspacemLabel
  | mprotect    : Addr → Size → Prot → AspacemLabel
  | shmat       : Addr → Size → Prot → AspacemLabel
  | brk_extend  : Addr → SSizeT → AspacemLabel    -- extend into reservation
  | mremap      : Addr → Size → Addr → Size → AspacemLabel
```

Where:
```
inductive Owner where | Client | Valgrind
structure Prot where (r w x : Bool)
structure FileInfo where (dev ino : UInt64) (offset : Int64) (name : Option String)
```

### 2.3 The Transition Relation

```
Tr : AspacemState → AspacemLabel → AspacemState → Prop
```

Each transition is defined by how `add_segment` transforms the segment array.
The key insight is that `add_segment` is *deterministic* given a valid
(state, label) pair: it splits at boundaries, replaces the spanned range,
and preens. The nondeterminism, if any, comes from `am_get_advisory` for
float mappings (choosing where to place an unconstrained allocation).

**Transition: mmap_anon(addr, size, prot, owner)**

Precondition: The range `[addr, addr+size-1]` must be coverable (for fixed:
the range must not overlap Valgrind segments if client, or client segments
if Valgrind; for float: some free range of sufficient size exists).

Effect: Create a new segment `{kind = SkAnon{C,V}, start = addr,
end = addr + size - 1, prot = (r,w,x)}`, call `add_segment`, which:
- Splits any segment straddling `addr` into two pieces.
- Splits any segment straddling `addr + size`.
- Replaces all segments in `[addr, addr+size-1]` with the new one.
- Preens (merges if the new segment is compatible with neighbors).

**Transition: munmap(addr, size)**

Effect: Create `{kind = SkFree, start = addr, end = addr+size-1}`,
call `add_segment`. Adjacent SkFree segments merge during preen.

Special case: if the unmapped range is above `aspacem_maxAddr` or below
`aspacem_minAddr`, the replacement segment is SkResvn instead of SkFree.

**Transition: mprotect(addr, size, prot)**

Effect: Split at boundaries, then for each segment in the range that is
a mapping (not SkFree, not SkResvn), update `hasR/hasW/hasX`. Preen
afterward since permission changes may enable merging.

**Transition: brk_extend(addr, delta)**

Effect: An SkAnonC segment at `addr` grows by `|delta|` bytes into an
adjacent SkResvn segment. The reservation shrinks correspondingly. The
reservation must remain at least one page. This models data segment
growth (positive delta) or stack growth (negative delta).

**Transition: mremap(old_addr, old_size, new_addr, new_size)**

Effect: The old range becomes SkFree, the new range becomes the mapping
with the old segment's properties. Implemented via
`VG_(am_relocate_nooverlap_client)`.

### 2.4 The LTS Definition

```lean
def aspacemLTS : LTS AspacemState AspacemLabel where
  init := initialState  -- from parsing /proc/self/maps at startup
  Tr := aspacemTransition
```

The initial state is constructed by `VG_(am_startup)` which reads
`/proc/self/maps` and calls `add_segment` for each kernel mapping, starting
from a single SkFree segment covering `[0, Addr_MAX]`.

---

## 3. Connection to Iris Separation Logic

### 3.1 The Auth/Fragment Pattern

The aspacemgr's segment array is a natural fit for Iris's *authoritative
resource algebra* pattern:

- **Authoritative element** (`●`): The full segment array, held in an
  invariant. This is the single source of truth for the address space layout.

- **Fragment elements** (`◯`): Individual segments or sub-ranges, handed
  out to threads/modules that need to know about specific regions.

The key resource algebra is a *map from address ranges to segment info*:

```
AspacemRA := Auth(FinMap(AddrRange, SegInfo))
```

Where `Auth(M)` is Iris's authoritative camera over a resource algebra `M`,
and `FinMap` is a finite map resource algebra with disjoint-union composition.

### 3.2 Why This Works

The aspacemgr invariants map directly to Iris separation logic concepts:

| Aspacemgr Invariant | Iris Concept |
|---------------------|--------------|
| Full coverage (INV-1) | The authoritative element covers the full domain |
| Non-overlapping (INV-2) | Separating conjunction of fragments (`∗`) |
| Segment well-formedness (INV-3) | Per-fragment predicate in the invariant |
| Normalization (INV-4) | Quotient on the RA (merge-equivalent states are equal) |
| Kernel consistency (INV-5) | Refinement relation to a "kernel model" LTS |

The separating conjunction `∗` is the formal version of "non-overlapping":
if thread A holds `seg(0x1000, 0x2000, SkAnonC, rwx)` and thread B holds
`seg(0x3000, 0x4000, SkFileC, r-x)`, then `A ∗ B` guarantees these
segments do not overlap. The composition operation on the FinMap RA is
disjoint union -- attempting to compose overlapping entries yields an
invalid element.

### 3.3 The Invariant

```
aspacem_inv(γ) := ∃ st : AspacemState,
    own γ (● st.toFinMap)
  ∗ ⌜well_formed_state st⌝
  ∗ ⌜consistent_with_kernel st⌝
```

This invariant lives in an Iris invariant namespace. It asserts:
1. The authoritative element `●` tracks the full segment map.
2. The state satisfies the structural invariants (INV-1 through INV-4).
3. The state is consistent with the kernel's actual mappings (INV-5).

### 3.4 Fragment Ownership

A fragment assertion `own γ (◯ {[a,b) ↦ seginfo})` gives a thread the
right to *know* that the range `[a,b)` currently has kind `seginfo`, and
the right to *participate in updates* to that range.

For example, the client heap manager might hold:
```
own γ (◯ {[heap_start, heap_end) ↦ SkAnonC(rw-)})
```

This gives it the authority to extend the heap (via brk_extend) because it
can open the invariant, check that the authoritative element agrees, perform
the update, and close the invariant -- all within an Iris atomic step.

### 3.5 Update Protocol

An mmap transition in Iris:

```
{aspacem_inv(γ) ∗ own γ (◯ {[a, a+n) ↦ SkFree})}
  do_mmap(a, n, prot)
{aspacem_inv(γ) ∗ own γ (◯ {[a, a+n) ↦ SkAnonC(prot)})}
```

The proof obligation is:
1. Open the invariant to get `● M`.
2. Check that `M` agrees with the fragment: `[a, a+n)` is indeed SkFree.
3. Perform a *frame-preserving update*: replace SkFree with SkAnonC in both
   `●` and `◯` simultaneously.
4. Re-establish well-formedness (the new state satisfies INV-1 through INV-4).
5. Close the invariant.

The frame-preserving update is valid because:
- The new authoritative element still covers the full domain (INV-1 preserved).
- No other fragment is invalidated (the range was SkFree, so no other
  thread held a fragment for it -- or if it did, it was also SkFree).
- The new segment is well-formed (INV-3).
- Preen-equivalence is maintained (INV-4).

### 3.6 The Advise/Notify Split in Iris

The aspacemgr's advise-then-notify protocol has a natural Iris reading:

1. **Advise phase** (`am_get_advisory`): Open the invariant *read-only*,
   consult the authoritative element to find a suitable placement, return
   the advisory. No update occurs. This is a *persistent* read.

2. **Kernel phase**: The actual `mmap` syscall. This is *outside* the Iris
   model -- it is the "real world" that the model tracks.

3. **Notify phase** (`am_notify_client_mmap`): Open the invariant, perform
   the frame-preserving update to record the kernel's result. This is the
   actual LTS transition.

The gap between advise and notify is where the kernel can reject or
relocate the mapping. The Iris model handles this by making the notify
transition conditional: it only fires if the kernel succeeded and the
result is compatible with the current state.

---

## 4. Comparison with Prior Art

### 4.1 seL4 Memory Model (Isabelle/HOL)

seL4 formalizes memory management through *capabilities* on *untyped
memory objects*. The key differences from aspacemgr:

| Aspect | seL4 | aspacemgr |
|--------|------|-----------|
| Granularity | Capability-based, object-level | Interval map, byte-level |
| Authority | Explicit capabilities in CDT | Implicit (C vs V ownership) |
| Verification | Full functional correctness | Runtime assertions only |
| Memory model | Flat in-kernel memory assumed consistent | Tracks user-space layout |

seL4's capability derivation tree (CDT) is a more structured authority
model. In aspacemgr, the C/V ownership distinction serves a similar
(but cruder) purpose: Valgrind segments are protected from client
operations, and vice versa. An Iris formalization of aspacemgr would
benefit from making this authority structure explicit via capabilities in
the resource algebra.

The seL4 proof famously *assumes* virtual memory consistency informally
rather than proving it. The VM subsystem receives special treatment: the C
semantics assumes a flat view of in-kernel memory that the VM subsystem
keeps consistent. This is exactly the gap that a formal aspacemgr model
could fill for a different system.

### 4.2 CertiKOS / BabyVMM (Coq)

CertiKOS decomposes the VMM into abstraction layers:
- Physical page allocation
- Page table drivers
- Address space API

Each layer provides an abstraction that the next utilizes, and the layers
are linked by compositional refinement. This is directly analogous to the
learnability project's convergence/refinement approach: the aspacemgr LTS
at one level of abstraction (segment array operations) refines a higher-level
specification (the set of valid address space configurations).

The BabyVMM verification in Coq proves that a simplified VMM correctly
implements virtual address translation. The aspacemgr is solving a related
but different problem: not address translation, but *layout tracking*.
CertiKOS's layer methodology is relevant to how we'd decompose the aspacemgr
proof into manageable pieces.

### 4.3 VMSL (Iris, Coq)

VMSL (PLDI 2023) is the closest prior art. It is a separation logic for
reasoning about virtual machines communicating via Arm's FF-A hypercall
interface. Key parallels:

- VMSL models an ISA where hypercalls are machine steps -- analogous to
  modeling syscalls (mmap/munmap/mprotect) as LTS transitions.
- VMSL proves *robust safety*: even compromised VMs cannot break safety
  properties of other VMs. The analog for aspacemgr is: even malicious
  client code cannot corrupt Valgrind's segments (the C/V ownership
  invariant).
- VMSL is mechanized in Coq using Iris. The aspacemgr formalization would
  follow the same path (or use iris-lean for Lean 4).

### 4.4 iris-lean

The `iris-lean` project (maintained by Mario Carneiro and Markus de Medeiros)
is a Lean 4 port of Iris providing MoSeL (the proof interface), uPred
(the base logic), and selected resource algebras. This means an
aspacemgr-in-Iris formalization could potentially live in the same Lean 4
ecosystem as the learnability project, using `iris-lean` for the separation
logic infrastructure and the project's existing `LTS` structure for the
transition system.

---

## 5. Concrete Formalization Plan

### Phase 1: Pure LTS (no Iris)

Define the aspacemgr LTS using the project's existing `Core.LTS` framework:

1. **NSegment and AspacemState** as Lean structures with the invariants as
   propositions.
2. **AspacemLabel** as an inductive type.
3. **aspacemTransition** as a relation `AspacemState → AspacemLabel → AspacemState → Prop`,
   defined case-by-case for each operation.
4. **Prove invariant preservation**: every transition preserves INV-1 through
   INV-4.
5. **Prove determinism** of `add_segment + preen` given a fixed label
   (the only nondeterminism is in float-map address selection).

This is self-contained and does not require Iris.

### Phase 2: Resource Algebra Construction

Define the resource algebra for address space segments:

1. **SegMapRA**: A finite map from `AddrRange` to `SegInfo` with disjoint-union
   composition. Two elements compose iff their domains don't overlap.
2. **Validity**: An element is valid iff its ranges are non-overlapping,
   page-aligned, and each segment is well-formed.
3. **Core**: The core of an element is itself (the RA is cancellative for
   non-overlapping maps).

This can be done with or without iris-lean. The RA axioms (associativity,
commutativity of composition, validity monotonicity) would be proved in Lean.

### Phase 3: Auth/Fragment Wiring (requires iris-lean or manual Iris encoding)

1. Wrap `SegMapRA` in the authoritative construction: `Auth(SegMapRA)`.
2. Define the aspacemgr invariant as an Iris invariant.
3. Prove the Hoare triples for each transition (mmap, munmap, mprotect, brk).
4. Show that fragment ownership provides meaningful guarantees: e.g.,
   holding `◯ {[a,b) ↦ SkAnonC(rw-)}` means no other thread can munmap
   or mprotect that range without updating the fragment.

### Phase 4: Refinement to Kernel Model

Connect the aspacemgr LTS to a model of the Linux kernel's mm subsystem:

1. Define a "kernel memory model" LTS with transitions for the actual
   syscalls.
2. Show that aspacemgr *simulates* the kernel model (every kernel transition
   has a corresponding aspacemgr transition that maintains consistency).
3. This is the formal version of INV-5 (sync check).

---

## 6. Why This Matters for Learnability

The aspacemgr is a compelling subject for the learnability framework because:

1. **It is a real, production-quality system** with carefully maintained
   invariants, not a toy example. The segment array has been stable for
   ~20 years.

2. **Its state space is finite and structured.** Unlike a general heap, the
   segment array is bounded (30000 entries) and sorted. This makes the LTS
   finite-state in practice.

3. **Its transitions are well-documented and deterministic** (modulo float
   placement). The source code comments are unusually detailed about the
   design rationale.

4. **The advise/notify protocol** is a natural two-phase commit that maps
   cleanly onto Iris's invariant-open/update/close pattern.

5. **It exercises the generic LTS layer** in a non-parser, non-interpreter
   domain. The aspacemgr is a *data structure manager* -- its LTS describes
   how a sorted interval map evolves under insertions, deletions, and
   permission changes. This is precisely the kind of diversity needed to
   validate that the generic LTS layer is not secretly grammar-shaped.

6. **The Iris connection is natural and non-trivial.** The segment array is
   an authoritative resource with fragments (individual segments) that can
   be distributed to threads. The non-overlapping invariant is literally
   the separating conjunction. This makes the aspacemgr a pedagogically
   ideal example of how LTS + separation logic compose.

7. **It connects to the broader verification landscape.** The seL4, CertiKOS,
   and VMSL projects all grapple with formalizing memory management. An
   aspacemgr LTS formalization in Lean 4 would be novel (no existing
   formalization of Valgrind's memory model exists) and would connect to
   these efforts.

---

## 7. Key Source Files

All paths relative to the Valgrind source root:

- `include/pub_tool_aspacemgr.h` -- NSegment, SegKind, ShrinkMode definitions; tool-visible API
- `coregrind/pub_core_aspacemgr.h` -- Core-internal API (notify operations, advisory, reservations)
- `coregrind/m_aspacemgr/priv_aspacemgr.h` -- Module-private declarations
- `coregrind/m_aspacemgr/aspacemgr-linux.c` -- The implementation (~3800 lines):
  - Lines 50-267: Design overview (essential reading)
  - Lines 278-342: State declarations (segment array, limits)
  - Lines 611-655: `sane_NSegment` (per-segment invariant check)
  - Lines 662-717: `maybe_merge_nsegments` (merge criterion)
  - Lines 723-756: `preen_nsegments` (normalization + invariant check)
  - Lines 1084-1154: `find_nsegment_idx` (binary search with cache)
  - Lines 1392-1426: `split_nsegment_at` (boundary splitting)
  - Lines 1468-1520: `add_segment` (core mutation operation)
  - Lines 2302-2347: `am_notify_client_mmap`
  - Lines 2393-2435: `am_notify_mprotect`
  - Lines 2445-2487: `am_notify_munmap`
  - Lines 2606-2661: `am_mmap_anon_fixed_client`
  - Lines 2667-2723: `am_mmap_anon_float_client`
  - Lines 3162-3262: `am_extend_into_adjacent_reservation_client`
- `coregrind/m_aspacemgr/aspacemgr-segnames.c` -- Segment name string table
- `coregrind/m_aspacemgr/aspacemgr-common.c` -- Platform-independent utilities

## References

- seL4 specification and proofs: https://github.com/seL4/l4v
- seL4 abstract formal specification: https://sel4.systems/Info/Docs/seL4-spec.pdf
- CertiKOS BabyVMM compositional verification: https://flint.cs.yale.edu/flint/publications/babyvmm_tr.pdf
- CertiKOS deep specifications: https://www.cs.cmu.edu/~15811/papers/certikos.pdf
- VMSL separation logic for VMs: https://askarov.net/vmsl.pdf (PLDI 2023)
- Iris lecture notes: https://cs.au.dk/~birke/papers/iris-lecture-notes.pdf
- Iris from the ground up: https://iris-project.org/
- iris-lean (Lean 4 port): https://github.com/leanprover-community/iris-lean
- Formal memory models for OS verification: https://link.springer.com/article/10.1007/s10817-009-9122-0
- Verification of programs in virtual memory using separation logic: https://unsworks.unsw.edu.au/handle/1959.4/51288
