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

-- ═══════════════════════════════════════════════════════════════════════════
-- Connection between ByteHeap (abstract) and ByteMem (concrete)
-- ═══════════════════════════════════════════════════════════════════════════

/-- A ByteHeap fragment is consistent with a concrete ByteMem:
    every owned byte in the fragment matches the concrete memory. -/
def ByteHeap.models (h : ByteHeap) (m : ByteMem) : Prop :=
  ∀ addr, match h addr with
    | some (.excl v) => m.fn addr = v
    | _ => True

/-- byteOwn models: owning byte `a` with value `v` means `m.fn a = v`. -/
theorem byteOwn_models (a : UInt64) (v : UInt8) (m : ByteMem)
    (h : (byteOwn a v).models m) : m.fn a = v := by
  have := h a
  simp [byteOwn] at this
  exact this

/-- Composing two valid fragments gives a larger fragment that models the same memory.
    This is the key soundness property: if fragment₁ and fragment₂ are both valid
    and both model the same concrete memory, their composition also models it. -/
theorem ByteHeap.models_op (h₁ h₂ : ByteHeap) (m : ByteMem)
    (_hv : CMRA.Valid (CMRA.op h₁ h₂))
    (hm₁ : h₁.models m) (hm₂ : h₂.models m) :
    (CMRA.op h₁ h₂).models m := by
  intro addr
  unfold models at *
  specialize hm₁ addr; specialize hm₂ addr
  -- CMRA.op on function store is pointwise optionOp
  show match optionOp (h₁ addr) (h₂ addr) with
    | some (.excl v) => m.fn addr = v | _ => True
  cases hh₁ : h₁ addr <;> cases hh₂ : h₂ addr
  · simp [optionOp]
  · simp [optionOp, hh₂] at hm₂ ⊢; exact hm₂
  · simp [optionOp, hh₁] at hm₁ ⊢; exact hm₁
  · simp [optionOp, CMRA.op]

/-- The frame property: if two byte ownerships are validly composed (disjoint),
    they must be at different addresses. This is non-aliasing from `∗`. -/
theorem byteOwn_ne_of_valid (a b : UInt64) (va vb : UInt8)
    (hv : CMRA.Valid (CMRA.op (byteOwn a va) (byteOwn b vb))) :
    a ≠ b := by
  intro heq; subst heq
  -- hv : ∀ k, optionValid (optionOp (byteOwn a va k) (byteOwn a vb k))
  -- At k = a: optionOp (some (excl va)) (some (excl vb)) = some invalid
  -- optionValid (some invalid) = False
  have := hv a
  simp only [byteOwn, optionOp, CMRA.op, Excl.Valid, optionValid,
    ite_true, CMRA.Valid] at this
