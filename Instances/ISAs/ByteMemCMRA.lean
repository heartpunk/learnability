import Iris
import Instances.ISAs.VexSyntax

/-!
# ByteMem Separation Algebra via Iris

ByteHeap = UInt64 → Option (Excl UInt8): a UCMRA where
- Addresses are UInt64 keys
- Byte values are exclusively owned (Excl UInt8)
- Composition is pointwise: two claims on the same address = invalid
- Non-aliasing is structural via separating conjunction
-/

open Iris VexISA

-- Discrete OFE instances for UInt8 and UInt64
instance : OFE UInt8 where
  Equiv := Eq
  Dist _ := Eq
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  equiv_dist := ⟨fun h _ => h, fun h => h 0⟩
  dist_lt h _ := h

instance : OFE UInt64 where
  Equiv := Eq
  Dist _ := Eq
  dist_eqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  equiv_dist := ⟨fun h _ => h, fun h => h 0⟩
  dist_lt h _ := h

-- The byte heap: partial map from UInt64 to exclusively-owned bytes.
-- This is a UCMRA via iris-lean's function-based Heap + Excl instances.
abbrev ByteHeap := UInt64 → Option (Excl UInt8)

-- Single-byte ownership: "I own the byte at address `a` with value `v`"
def byteOwn (a : UInt64) (v : UInt8) : ByteHeap :=
  fun k => if k = a then some (.excl v) else none
