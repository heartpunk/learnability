# Plan: ByteMem Refactor — List → Function

## Problem

`ByteMem := List (UInt64 × UInt8)` is an association list. Two writes at the same address in different orders produce different lists representing the same memory. This makes `writeByte_writeByte_comm` and `writeLEAux_writeLEAux_same` unprovable as list equality, blocking the dead-store elimination soundness proof in `simplifyLoadStoreMem_sound`.

## Solution

Change `ByteMem := UInt64 → UInt8`. A function from addresses to byte values. `writeByte` becomes `fun b => if b = addr then value else mem b`. `readByte` becomes `mem addr`. All equality is extensional via `funext`.

## Why This Works

- `writeByte_writeByte_same`: `funext b; split; rfl` — if `b = a`, both return `v2`; otherwise both return `mem b`.
- `writeByte_writeByte_comm`: `funext c; by_cases c = a; by_cases c = b; simp` — standard `if` commutation.
- `writeLEAux_writeLEAux_same`: induction on `n`, using `writeByte_writeByte_comm` to commute `writeByte(addr+k)` past `writeLEAux` range `0..k-1`, then `writeByte_writeByte_same` to collapse, then IH.

## Why Not HashMap/Finmap

- `Std.HashMap` doesn't have extensional equality (two maps with same entries might not be `=`)
- `Finmap` from Mathlib works but adds a heavy dependency for what's purely a proof-side type
- The function representation is simplest and gives the strongest equational theory

## Why Not Word-Level

`ByteMem` as `(UInt64 × Width) → UInt64` would match `SymMem`'s store chain structure but requires handling partial overlaps between different widths in the proofs. The existing byte-level decomposition (`writeLEAux`, `readLEAux`) already handles width conversion. Changing to word-level would require rethinking all the load-after-store resolution proofs. Save for the real memory model.

## Files Affected

### VexSyntax.lean (primary)
- `ByteCell` — remove (no longer needed)
- `ByteMem` — change from `List ByteCell` to `UInt64 → UInt8`
- `ByteMem.empty` — change from `[]` to `fun _ => 0`
- `ByteMem.eraseAddr` — remove entirely (not needed with function rep)
- `ByteMem.readByte` — change from list search to `mem addr`
- `ByteMem.writeByte` — change from cons+eraseAddr to `fun b => if b = a then v else mem b`
- `ByteMem.writeLEAux` — unchanged (still recursive writeByte chain)
- `ByteMem.readLEAux` — unchanged (still recursive readByte chain)
- `ByteMem.read/write` — unchanged (still dispatch on Width)
- All read-after-write lemmas — reprove (should be simpler)
- Add: `writeByte_writeByte_comm`, `writeByte_writeLEAux_comm`, `writeLEAux_writeLEAux_same`, `ByteMem_write_write_same`

### VexSimplificationSoundness.lean
- `resolveLoadFrom_sound` — lemma proofs should still work (they use `readByte_writeByte_ne` etc.)
- `simplifyLoadStoreMem_sound` — dead store case now provable via `ByteMem_write_write_same`
- `simplifyLoadStoreExpr_sound` — cascading sorry resolves automatically

### VexConcrete.lean (check)
- `ConcreteState` uses `ByteMem` for memory — type changes but operations stay same
- `evalSymMem` returns `ByteMem` — return type changes

### Other files
- Grep for `ByteMem` and `ByteCell` across codebase to find any other references
- Tier0-Tier8 examples may reference `ByteMem.empty` — update to new definition

## Known Issue: `addr + UInt64.ofNat i ≠ addr + UInt64.ofNat k` for `i < k`

The `writeByte_writeLEAux_comm` lemma needs `addr+i ≠ addr+k` for `i < k`. This is NOT true in general for UInt64 (wrapping). But all uses have `k < 8` (max width). Two approaches:

1. **Add bound hypothesis**: `writeByte_writeLEAux_comm` takes `n < UInt64.size` (trivially satisfied for widths ≤ 8). Then `addr+i = addr+k` implies `i = k` (by `uint64_add_left_cancel`), contradicting `i < k`.

2. **Prove via `uint64_add_left_cancel`**: If `addr + UInt64.ofNat i = addr + UInt64.ofNat k`, then by cancellation `UInt64.ofNat i = UInt64.ofNat k`. Since `i, k < 8 < 2^64`, `UInt64.ofNat` is injective, so `i = k`, contradicting `i < k`. This works without any extra hypothesis.

Approach 2 is cleaner. The `uint64_add_left_cancel` lemma is already proved.

## Execution Order

1. Change `ByteMem` type and `readByte`/`writeByte`/`empty`/remove `eraseAddr` in VexSyntax.lean
2. Reprove `readByte_writeByte_same`, `readByte_writeByte_ne` (trivial with new rep)
3. Reprove `readByte_writeLEAux_nonoverlap` (induction, same structure, easier base case)
4. Reprove `readLEAux_writeLEAux_nonoverlap`, `readLEAux_writeByte_nonoverlap` (same)
5. Reprove `read_write_same_w{8,16,32,64}` (same structure)
6. Reprove `ByteMem_read_write_same`, `ByteMem_read_write_nonoverlap` (same)
7. Add `writeByte_writeByte_comm` (funext + if-splitting)
8. Add `writeByte_writeLEAux_comm` (induction + writeByte_writeByte_comm)
9. Add `writeLEAux_writeLEAux_same` (induction + comm + writeByte_writeByte_same)
10. Add `ByteMem_write_write_same` (cases on Width + above)
11. Fix `simplifyLoadStoreMem_sound` dead store case using `ByteMem_write_write_same`
12. Fix any downstream breakage (VexConcrete, examples)
13. Full `lake build` — should drop from 4 to 2 sorry warnings

## What This Unblocks

- `simplifyLoadStoreMem_sound` dead store case (currently sorry)
- `simplifyLoadStoreExpr_sound` cascading sorry (depends on above)
- Drops sorry count from 4 → 2 (remaining: VexPipelineBridge Finset intro, TemplateConvergence Finset intro)
