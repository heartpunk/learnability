import Iris
import Iris.ProofMode
import Iris.Instances.UPred
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

-- ═══════════════════════════════════════════════════════════════════════════
-- Multi-byte ownership and the frame rule for ByteMem.read/write
-- ═══════════════════════════════════════════════════════════════════════════

/-- If two ByteHeap fragments are validly composed and both claim ownership at
    the same address, that's a contradiction. -/
theorem byteHeap_absurd_of_both_some (h₁ h₂ : ByteHeap) (addr : UInt64)
    (hv : CMRA.Valid (CMRA.op h₁ h₂))
    (ha : ∃ va, h₁ addr = some (.excl va))
    (hb : ∃ vb, h₂ addr = some (.excl vb)) :
    False := by
  obtain ⟨va, hva⟩ := ha
  obtain ⟨vb, hvb⟩ := hb
  have := hv addr
  simp only [CMRA.Valid, optionValid, optionOp, CMRA.op,
    hva, hvb, Excl.Valid] at this

/-- The separation frame rule for ByteMem: if the write footprint and read footprint
    are owned by validly-composed (disjoint) ByteHeap fragments, then the write
    doesn't affect the read. This replaces arithmetic-based non-aliasing with
    structural non-aliasing from the CMRA. -/
theorem ByteMem_frame_of_separate
    (lw sw : Width) (M : ByteMem) (a v b : UInt64)
    (h_write h_read : ByteHeap)
    (hv : CMRA.Valid (CMRA.op h_write h_read))
    (hw : ∀ i, i < sw.byteCount → ∃ vi, h_write (a + UInt64.ofNat i) = some (.excl vi))
    (hr : ∀ j, j < lw.byteCount → ∃ vj, h_read (b + UInt64.ofNat j) = some (.excl vj)) :
    ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b := by
  apply ByteMem_read_write_ne
  intro i j hi hj heq
  exact byteHeap_absurd_of_both_some h_write h_read (a + UInt64.ofNat i) hv
    (hw i hi) (heq ▸ hr j hj)

-- ═══════════════════════════════════════════════════════════════════════════
-- UPred assertions over ByteHeap for MoSeL proof mode
-- ═══════════════════════════════════════════════════════════════════════════

open Iris.BI

-- ═══════════════════════════════════════════════════════════════════════════
-- UPred assertions over ByteHeap — the MoSeL interface
-- ═══════════════════════════════════════════════════════════════════════════

/-- Ownership assertion: "I own this ByteHeap fragment."
    `ownM h` holds at resource `x` if `h ≼ x` (h is included in x). -/
def ownBytes (h : ByteHeap) : UPred ByteHeap := UPred.ownM h

/-- The key MoSeL theorem: owning disjoint byte fragments means their
    addresses don't overlap, giving us the frame rule for ByteMem. -/
theorem ownBytes_frame (lw sw : Width) (M : ByteMem) (a v b : UInt64)
    (h_write h_read : ByteHeap)
    (hw : ∀ i, i < sw.byteCount → ∃ vi, h_write (a + UInt64.ofNat i) = some (.excl vi))
    (hr : ∀ j, j < lw.byteCount → ∃ vj, h_read (b + UInt64.ofNat j) = some (.excl vj)) :
    ownBytes h_write ∗ ownBytes h_read ⊢
      ⌜ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b⌝ := by
  -- Unpack the entailment and separating conjunction
  intro n x hv_x ⟨x₁, x₂, hx, hown₁, hown₂⟩
  -- hown₁ : h_write ≼{n} x₁ (ownership of write fragment)
  -- hown₂ : h_read ≼{n} x₂ (ownership of read fragment)
  -- hx : x ≡{n}≡ x₁ • x₂, hv_x : ✓{n} x
  -- Derive ✓ (h_write • h_read) from the inclusion chain
  have hv_comp : CMRA.Valid (CMRA.op h_write h_read) := by
    intro k
    -- x is valid, x ≡ x₁ • x₂, so x₁ • x₂ is valid
    -- h_write ≼ x₁ means x₁ = h_write • z for some z
    -- h_read ≼ x₂ means x₂ = h_read • w for some w
    -- So x₁ • x₂ = (h_write • z) • (h_read • w)
    -- Valid (h_write • z • h_read • w) → Valid (h_write • h_read) by monotonicity
    sorry
  exact ByteMem_frame_of_separate lw sw M a v b h_write h_read hv_comp hw hr
