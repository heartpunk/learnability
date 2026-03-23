import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

inductive Width where
  /-- 8-bit memory/register width. -/
  | w8
  /-- 16-bit memory/register width. -/
  | w16
  /-- 32-bit memory/register width. -/
  | w32
  /-- 64-bit memory/register width. -/
  | w64
  deriving DecidableEq, Repr

namespace Width

@[simp] def byteCount : Width → Nat
  | .w8 => 1
  | .w16 => 2
  | .w32 => 4
  | .w64 => 8

@[simp] def mask : Width → UInt64
  | .w8 => 0xFF
  | .w16 => 0xFFFF
  | .w32 => 0xFFFF_FFFF
  | .w64 => 0xFFFF_FFFF_FFFF_FFFF

end Width

@[simp] def truncate (width : Width) (value : UInt64) : UInt64 :=
  value &&& width.mask

def mask32 (value : UInt64) : UInt64 :=
  value &&& 0xFFFF_FFFF

/-! ### UInt64 arithmetic lemmas for frame reasoning -/

@[simp] theorem UInt64.size_eq : UInt64.size = 18446744073709551616 := by native_decide
theorem Nat.two_pow_64 : (2 : Nat) ^ 64 = 18446744073709551616 := by native_decide

-- toNat of UInt64.ofNat using UInt64.size (not 2^64, which omega can't handle)
@[simp] theorem UInt64.toNat_ofNat' (n : Nat) :
    (UInt64.ofNat n).toNat = n % UInt64.size := by
  have : UInt64.size = 2 ^ 64 := by native_decide
  simp [UInt64.ofNat, UInt64.toNat, this]

-- UInt64 arithmetic canonicalization: fold chained +/- into single offset.
-- `(a + c1) + c2 = a + (c1 + c2)` and `(a + c1) - c2 = a + (c1 - c2)` etc.
-- These let simp collapse addresses like `rbp + 8 + 8 - 72` to `rbp + (N-56)`.
theorem UInt64.add_assoc (a b c : UInt64) : a + b + c = a + (b + c) := by
  simp only [UInt64.add_def, BitVec.add_assoc]

theorem UInt64.sub_add (a b c : UInt64) : a - b + c = a + (c - b) := by
  have : a.toBitVec - b.toBitVec + c.toBitVec = a.toBitVec + (c.toBitVec - b.toBitVec) := by
    bv_omega
  exact congrArg UInt64.ofBitVec this

theorem UInt64.add_sub (a b c : UInt64) : a + b - c = a + (b - c) := by
  have : a.toBitVec + b.toBitVec - c.toBitVec = a.toBitVec + (b.toBitVec - c.toBitVec) := by
    bv_omega
  exact congrArg UInt64.ofBitVec this

-- Normalize .toBitVec.toNat to .toNat (they're definitionally equal but
-- simp sometimes produces one vs the other, breaking rw matching).
@[simp] theorem UInt64.toBitVec_toNat (a : UInt64) :
    a.toBitVec.toNat = a.toNat := rfl

@[simp] theorem UInt64.toNat_sub_of_le {a b : UInt64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  exact _root_.UInt64.toNat_sub_of_le a b h

-- Unconditional modular subtraction: (a - b).toNat = (a.toNat + 2^64 - b.toNat) % 2^64
theorem UInt64.toNat_sub (a b : UInt64) :
    (a - b).toNat = (a.toNat + UInt64.size - b.toNat) % UInt64.size := by
  have ha : a.toNat < UInt64.size := a.toBitVec.isLt
  have hb : b.toNat < UInt64.size := b.toBitVec.isLt
  change (a.toBitVec - b.toBitVec).toNat = _
  rw [BitVec.toNat_sub]
  simp only [UInt64.toBitVec_toNat, UInt64.size] at *
  omega

@[simp] theorem UInt64.toNat_add_of_lt {a b : UInt64} (h : a.toNat + b.toNat < UInt64.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp [_root_.UInt64.toNat_add]
  omega

@[simp] theorem mask32_sub (a b : UInt64) : mask32 (mask32 a - mask32 b) = mask32 (a - b) := by
  simp only [mask32]; bv_decide

@[simp] theorem mask32_add (a b : UInt64) : mask32 (mask32 a + mask32 b) = mask32 (a + b) := by
  simp only [mask32]; bv_decide

@[simp] theorem mask32_idempotent (v : UInt64) : mask32 (mask32 v) = mask32 v := by
  show v &&& 0xFFFF_FFFF &&& 0xFFFF_FFFF = v &&& 0xFFFF_FFFF
  rw [UInt64.and_assoc, UInt64.and_self]

/--
Interpret the low 8 bits of `value` as a signed byte, sign-extend that byte to 32 bits, then
store the resulting 32-bit bit-pattern in `UInt64` by clearing bits 63:32.
-/
@[simp] def signExtend8to32 (value : UInt64) : UInt64 :=
  let low := truncate .w8 value
  if low &&& 0x80 = 0 then
    low
  else
    mask32 (low ||| 0xFFFF_FF00)

/--
Interpret the low 32 bits of `value` as a signed 32-bit integer and sign-extend that bit-pattern
to the full 64-bit `UInt64` result.
-/
@[simp] def signExtend32to64 (value : UInt64) : UInt64 :=
  let low := mask32 value
  if low &&& 0x8000_0000 = 0 then
    low
  else
    low ||| 0xFFFF_FFFF_0000_0000

/-- Make 64-bit shift-count reduction explicit instead of relying on `UInt64.shift*`. -/
@[simp] def maskShift64 (amount : UInt64) : UInt64 :=
  amount &&& 0x3F

@[simp] def maskShift32 (amount : UInt64) : UInt64 :=
  amount &&& 0x1F

@[simp] def shiftLeft32 (value amount : UInt64) : UInt64 :=
  mask32 (UInt64.shiftLeft (mask32 value) (maskShift32 amount))

@[simp] def shiftLeft64 (value amount : UInt64) : UInt64 :=
  UInt64.shiftLeft value (maskShift64 amount)

@[simp] def shiftRight64 (value amount : UInt64) : UInt64 :=
  UInt64.shiftRight value (maskShift64 amount)

/-- Signed arithmetic right shift on 64-bit value.
    Sign bit is replicated into vacated positions. -/
@[simp] def signedShiftRight64 (value amount : UInt64) : UInt64 :=
  let n := (maskShift64 amount).toNat
  let signBit := value.toNat / (2 ^ 63)
  let shifted := value.toNat / (2 ^ n)
  if signBit == 1 then
    -- Fill top n bits with 1s
    let mask := (2 ^ 64 - 1) - (2 ^ (64 - n) - 1)
    UInt64.ofNat (shifted ||| mask)
  else
    UInt64.ofNat shifted

/-- Signed arithmetic right shift on 32-bit value, zero-extended to 64. -/
@[simp] def signedShiftRight32 (value amount : UInt64) : UInt64 :=
  let v32 := value.toNat % (2 ^ 32)
  let n := (amount.toNat % 32)
  let signBit := v32 / (2 ^ 31)
  let shifted := v32 / (2 ^ n)
  if signBit == 1 then
    let mask := (2 ^ 32 - 1) - (2 ^ (32 - n) - 1)
    UInt64.ofNat ((shifted ||| mask) % (2 ^ 32))
  else
    UInt64.ofNat shifted

abbrev ByteCell := UInt64 × UInt8

/-! ### ByteMem: total-function memory with sorted-list backing for decidable equality -/

private def ByteMem.lookupEntries : List (UInt64 × UInt8) → UInt64 → Option UInt8
  | [], _ => none
  | (k, v) :: rest, addr => if addr = k then some v else ByteMem.lookupEntries rest addr

private def ByteMem.insertSorted : List (UInt64 × UInt8) → UInt64 → UInt8 → List (UInt64 × UInt8)
  | [], addr, val => [(addr, val)]
  | (k, v) :: rest, addr, val =>
    if addr.toNat < k.toNat then (addr, val) :: (k, v) :: rest
    else if addr = k then (addr, val) :: rest
    else (k, v) :: ByteMem.insertSorted rest addr val

private theorem ByteMem.lookupEntries_insertSorted_same
    (entries : List (UInt64 × UInt8)) (addr : UInt64) (val : UInt8) :
    ByteMem.lookupEntries (ByteMem.insertSorted entries addr val) addr = some val := by
  induction entries with
  | nil => simp [insertSorted, lookupEntries]
  | cons hd tl ih =>
    simp only [insertSorted]
    split -- addr.toNat < hd.1.toNat
    · simp [lookupEntries]
    · split -- addr = hd.1
      · simp [lookupEntries]
      · -- addr > hd.1: recurse past hd
        simp only [lookupEntries]
        -- addr ≠ hd.1 follows from ¬(addr.toNat < hd.1.toNat) ∧ ¬(addr = hd.1)
        rename_i h1 h2
        simp [h2, ih]

private theorem ByteMem.lookupEntries_insertSorted_ne
    (entries : List (UInt64 × UInt8)) (a b : UInt64) (val : UInt8) (h : a ≠ b) :
    ByteMem.lookupEntries (ByteMem.insertSorted entries a val) b =
    ByteMem.lookupEntries entries b := by
  induction entries with
  | nil => simp [insertSorted, lookupEntries, Ne.symm h]
  | cons hd tl ih =>
    simp only [insertSorted]
    split -- a.toNat < hd.1.toNat
    · -- inserted before hd
      simp only [lookupEntries, Ne.symm h, ite_false]
    · split -- a = hd.1
      · -- replaced hd
        rename_i _ heq; subst heq
        simp [lookupEntries, Ne.symm h]
      · -- recurse past hd
        simp only [lookupEntries]; split
        · rfl
        · exact ih

private theorem ByteMem.insertSorted_insertSorted_same
    (entries : List (UInt64 × UInt8)) (addr : UInt64) (v1 v2 : UInt8) :
    ByteMem.insertSorted (ByteMem.insertSorted entries addr v1) addr v2 =
    ByteMem.insertSorted entries addr v2 := by
  induction entries with
  | nil =>
    simp only [insertSorted]
    have : ¬(addr.toNat < addr.toNat) := Nat.lt_irrefl _
    simp
  | cons hd tl ih =>
    simp only [insertSorted]
    split -- addr.toNat < hd.1.toNat
    · -- inserted before hd; now insert again at same position
      rename_i h1
      simp only [insertSorted, show ¬(addr.toNat < addr.toNat) from Nat.lt_irrefl _, ite_false,
        ite_true]
    · split -- addr = hd.1
      · -- replaced hd; now replace again
        simp only [insertSorted, show ¬(addr.toNat < addr.toNat) from Nat.lt_irrefl _, ite_false,
          ite_true]
      · -- recurse past hd
        rename_i h1 h2
        simp only [insertSorted, h1, h2, ite_false]
        exact congrArg _ ih

private theorem ByteMem.insertSorted_insertSorted_comm
    (entries : List (UInt64 × UInt8)) (a b : UInt64) (va vb : UInt8) (hab : a ≠ b) :
    ByteMem.insertSorted (ByteMem.insertSorted entries a va) b vb =
    ByteMem.insertSorted (ByteMem.insertSorted entries b vb) a va := by
  induction entries with
  | nil =>
    simp only [insertSorted]
    have hne : a.toNat ≠ b.toNat := fun h => hab (by
      exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
    by_cases h1 : a.toNat < b.toNat
    · have h2 : ¬(b.toNat < a.toNat) := by omega
      have h3 : ¬(b = a) := Ne.symm hab
      have h4 : ¬(a = b) := hab
      simp [h1, h2, h3]
    · have h2 : b.toNat < a.toNat := by omega
      have h3 : ¬(a.toNat < b.toNat) := by omega
      have h4 : ¬(b = a) := Ne.symm hab
      have h5 : ¬(a = b) := hab
      simp [h1, h2, h5]
  | cons hd tl ih =>
    have hne : a.toNat ≠ b.toNat := fun h => hab (by
      exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h))
    have hba : b ≠ a := Ne.symm hab
    simp only [insertSorted]
    by_cases ha1 : a.toNat < hd.1.toNat <;> by_cases ha2 : a = hd.1 <;>
      by_cases hb1 : b.toNat < hd.1.toNat <;> by_cases hb2 : b = hd.1
    -- Simplify remaining goals
    all_goals (try simp_all only [ite_true, ite_false, insertSorted])
    -- Close: rfl, IH (congr 1 splits cons equality into head + tail)
    all_goals (try simp only [Prod.eta] at *)
    all_goals (first | rfl | exact congrArg _ ih
                     | (split <;> (simp_all (config := { decide := false }) <;> omega))
                     | simp_all
                     | omega)

structure ByteMem where
  fn : UInt64 → UInt8
  entries : List (UInt64 × UInt8)
  h_agree : ∀ addr, fn addr = (ByteMem.lookupEntries entries addr).getD 0

private theorem ByteMem.eq_of_entries_eq {m1 m2 : ByteMem}
    (h : m1.entries = m2.entries) : m1 = m2 := by
  have hf : m1.fn = m2.fn := funext fun addr => by rw [m1.h_agree, m2.h_agree, h]
  cases m1; cases m2; subst hf; subst h; rfl

instance : DecidableEq ByteMem := fun m1 m2 =>
  if h : m1.entries = m2.entries then
    isTrue (ByteMem.eq_of_entries_eq h)
  else
    isFalse (fun heq => h (congrArg ByteMem.entries heq))

def ByteMem.empty : ByteMem :=
  ⟨fun _ => 0, [], by simp [lookupEntries]⟩

instance : EmptyCollection ByteMem := ⟨ByteMem.empty⟩

@[simp] def ByteMem.readByte (mem : ByteMem) (addr : UInt64) : UInt8 :=
  mem.fn addr

def ByteMem.writeByte (mem : ByteMem) (addr : UInt64) (value : UInt8) : ByteMem :=
  ⟨Function.update mem.fn addr value,
   ByteMem.insertSorted mem.entries addr value,
   fun a => by
    simp only [Function.update]
    split
    · next heq => subst heq; simp [lookupEntries_insertSorted_same]
    · next hne =>
      rw [mem.h_agree a, lookupEntries_insertSorted_ne mem.entries addr a value (Ne.symm hne)]⟩

def ByteMem.readLEAux (mem : ByteMem) (addr : UInt64) : Nat → UInt64
  | 0 => 0
  | n + 1 =>
      let rest := ByteMem.readLEAux mem addr n
      let byte := UInt64.ofNat ((ByteMem.readByte mem (addr + UInt64.ofNat n)).toNat)
      rest ||| UInt64.shiftLeft byte (UInt64.ofNat (8 * n))

@[simp] def ByteMem.read8 (mem : ByteMem) (addr : UInt64) : UInt64 :=
  UInt64.ofNat ((ByteMem.readByte mem addr).toNat)

def ByteMem.read16le (mem : ByteMem) (addr : UInt64) : UInt64 :=
  ByteMem.readLEAux mem addr 2

def ByteMem.read32le (mem : ByteMem) (addr : UInt64) : UInt64 :=
  ByteMem.readLEAux mem addr 4

def ByteMem.read64le (mem : ByteMem) (addr : UInt64) : UInt64 :=
  ByteMem.readLEAux mem addr 8

@[simp] def ByteMem.read : Width → ByteMem → UInt64 → UInt64
  | .w8, mem, addr => ByteMem.read8 mem addr
  | .w16, mem, addr => ByteMem.read16le mem addr
  | .w32, mem, addr => ByteMem.read32le mem addr
  | .w64, mem, addr => ByteMem.read64le mem addr

def ByteMem.writeLEAux (mem : ByteMem) (addr value : UInt64) : Nat → ByteMem
  | 0 => mem
  | n + 1 =>
      let shifted := UInt64.shiftRight value (UInt64.ofNat (8 * n))
      let byte := UInt8.ofNat (UInt64.toNat shifted)
      ByteMem.writeLEAux (ByteMem.writeByte mem (addr + UInt64.ofNat n) byte) addr value n

def ByteMem.write8 (mem : ByteMem) (addr value : UInt64) : ByteMem :=
  ByteMem.writeByte mem addr (UInt8.ofNat (UInt64.toNat value))

def ByteMem.write16le (mem : ByteMem) (addr value : UInt64) : ByteMem :=
  ByteMem.writeLEAux mem addr value 2

def ByteMem.write32le (mem : ByteMem) (addr value : UInt64) : ByteMem :=
  ByteMem.writeLEAux mem addr value 4

def ByteMem.write64le (mem : ByteMem) (addr value : UInt64) : ByteMem :=
  ByteMem.writeLEAux mem addr value 8

@[simp] def ByteMem.write : Width → ByteMem → UInt64 → UInt64 → ByteMem
  | .w8, mem, addr, value => ByteMem.write8 mem addr value
  | .w16, mem, addr, value => ByteMem.write16le mem addr value
  | .w32, mem, addr, value => ByteMem.write32le mem addr value
  | .w64, mem, addr, value => ByteMem.write64le mem addr value

inductive Expr (Reg : Type) where
  /-- Literal 64-bit constant. -/
  | const : UInt64 → Expr Reg
  /-- Read the current value of a machine register. -/
  | get : Reg → Expr Reg
  /-- Read the current value of a temporary SSA slot. -/
  | tmp : Nat → Expr Reg
  /-- Keep only the low 32 bits of the input and return them as a `UInt64`. -/
  | narrow32 : Expr Reg → Expr Reg
  /--
  Treat the input as a 32-bit quantity embedded in `UInt64` and zero-extend it by discarding
  any high bits above bit 31.
  -/
  | zext64 : Expr Reg → Expr Reg
  /--
  Interpret the low 8 bits of the input as a signed byte, sign-extend that byte to 32 bits, then
  return the resulting 32-bit bit-pattern as a zero-extended `UInt64`.
  -/
  | sext8to32 : Expr Reg → Expr Reg
  /--
  Interpret the low 32 bits of the input as a signed 32-bit integer, then sign-extend that
  bit-pattern to the full 64-bit `UInt64` result.
  -/
  | sext32to64 : Expr Reg → Expr Reg
  /--
  Add the low 32 bits of both operands modulo `2^32`, then return the wrapped result as a
  zero-extended `UInt64`.
  -/
  | add32 : Expr Reg → Expr Reg → Expr Reg
  /--
  Subtract the low 32 bits of the right operand from the low 32 bits of the left operand modulo
  `2^32`, then return the wrapped result as a zero-extended `UInt64`.
  -/
  | sub32 : Expr Reg → Expr Reg → Expr Reg
  /--
  Logical left shift on the low 32 bits of the input. The value is truncated to 32 bits before
  shifting, the shift count is reduced modulo 32 by masking with `0x1F`, and the final result is
  returned as a zero-extended `UInt64`.
  -/
  | shl32 : Expr Reg → Expr Reg → Expr Reg
  /-- Bitwise AND on the low 32 bits, zero-extended to 64-bit. -/
  | and32 : Expr Reg → Expr Reg → Expr Reg
  | or32 : Expr Reg → Expr Reg → Expr Reg
  | xor32 : Expr Reg → Expr Reg → Expr Reg
  /-- Add two 64-bit words with `UInt64` wraparound semantics. -/
  | add64 : Expr Reg → Expr Reg → Expr Reg
  /-- Subtract two 64-bit words with `UInt64` wraparound semantics. -/
  | sub64 : Expr Reg → Expr Reg → Expr Reg
  /-- Bitwise exclusive-or on 64-bit words. -/
  | xor64 : Expr Reg → Expr Reg → Expr Reg
  /-- Bitwise and on 64-bit words. -/
  | and64 : Expr Reg → Expr Reg → Expr Reg
  /-- Bitwise or on 64-bit words. -/
  | or64 : Expr Reg → Expr Reg → Expr Reg
  /--
  Logical left shift on a 64-bit word. Shift counts are reduced modulo 64 by masking with
  `0x3F` before shifting.
  -/
  | shl64 : Expr Reg → Expr Reg → Expr Reg
  /--
  Logical right shift on a 64-bit word. Shift counts are reduced modulo 64 by masking with
  `0x3F` before shifting.
  -/
  | shr64 : Expr Reg → Expr Reg → Expr Reg
  /-- Multiply two 64-bit words with `UInt64` wraparound semantics. -/
  | mul64 : Expr Reg → Expr Reg → Expr Reg
  | mul32 : Expr Reg → Expr Reg → Expr Reg
  | not64 : Expr Reg → Expr Reg
  | not32 : Expr Reg → Expr Reg
  | sar64 : Expr Reg → Expr Reg → Expr Reg
  | sar32 : Expr Reg → Expr Reg → Expr Reg
  /-- Conditional expression: if cond ≠ 0 then trueVal else falseVal. -/
  | ite : Expr Reg → Expr Reg → Expr Reg → Expr Reg
  /--
  Read `width` bits from memory in little-endian order at the computed address, then zero-extend
  the result to `UInt64`. Missing bytes default to `0` because `ByteMem.readByte` zero-fills
  absent cells.
  -/
  | load : Width → Expr Reg → Expr Reg
  deriving DecidableEq, Repr

namespace Expr

@[match_pattern] abbrev low32 {Reg : Type} (expr : Expr Reg) : Expr Reg :=
  .narrow32 expr

@[match_pattern] abbrev uext32 {Reg : Type} (expr : Expr Reg) : Expr Reg :=
  .zext64 expr

end Expr

inductive Cond (Reg : Type) where
  /-- Compare two 64-bit expressions for equality. -/
  | eq64 : Expr Reg → Expr Reg → Cond Reg
  /-- Unsigned 64-bit less-than comparison on `UInt64` values. -/
  | lt64 : Expr Reg → Expr Reg → Cond Reg
  /-- Unsigned 64-bit less-than-or-equal comparison on `UInt64` values. -/
  | le64 : Expr Reg → Expr Reg → Cond Reg
  /-- 64-bit not-equal comparison (negation of eq64). -/
  | ne64 : Expr Reg → Expr Reg → Cond Reg
  /--
  Partial AMD64 condition-code helper. The current semantics only implement the zero-condition
  slice used by the existing `jz`-style fixtures; unsupported codes evaluate to `false`.
  -/
  | amd64CalculateCondition : UInt64 → Expr Reg → Expr Reg → Expr Reg → Expr Reg → Cond Reg
  deriving DecidableEq, Repr

inductive LinearStmt (Reg : Type) where
  | wrTmp : Nat → Expr Reg → LinearStmt Reg
  | put : Reg → Expr Reg → LinearStmt Reg
  /--
  Store the low `width` bits of the value at the computed address in little-endian byte order.
  Higher bytes in memory are left unchanged.
  -/
  | store : Width → Expr Reg → Expr Reg → LinearStmt Reg
  deriving DecidableEq, Repr

inductive BranchStmt (Reg : Type) where
  | exit : Cond Reg → UInt64 → BranchStmt Reg
  deriving DecidableEq, Repr

inductive Stmt (Reg : Type) where
  | linear : LinearStmt Reg → Stmt Reg
  | branch : BranchStmt Reg → Stmt Reg
  deriving DecidableEq, Repr

namespace Stmt

@[match_pattern] abbrev wrTmp {Reg : Type} (tmp : Nat) (expr : Expr Reg) : Stmt Reg :=
  .linear (.wrTmp tmp expr)

@[match_pattern] abbrev put {Reg : Type} (reg : Reg) (expr : Expr Reg) : Stmt Reg :=
  .linear (.put reg expr)

@[match_pattern] abbrev store {Reg : Type} (width : Width) (addr value : Expr Reg) : Stmt Reg :=
  .linear (.store width addr value)

@[match_pattern] abbrev exit {Reg : Type} (cond : Cond Reg) (target : UInt64) : Stmt Reg :=
  .branch (.exit cond target)

end Stmt

structure Block (Reg : Type) where
  stmts : List (Stmt Reg)
  ip_reg : Reg
  next : UInt64
  deriving DecidableEq, Repr

structure ConcreteState (Reg : Type) where
  regs : Reg → UInt64
  mem : ByteMem

instance {Reg : Type} [DecidableEq Reg] [Fintype Reg] : DecidableEq (ConcreteState Reg) := by
  intro state₁ state₂
  by_cases hRegs : state₁.regs = state₂.regs
  · by_cases hMem : state₁.mem = state₂.mem
    · cases state₁
      cases state₂
      cases hRegs
      cases hMem
      exact isTrue rfl
    · exact isFalse (fun h => hMem (congrArg ConcreteState.mem h))
  · exact isFalse (fun h => hRegs (congrArg ConcreteState.regs h))

@[ext] theorem ConcreteState.ext {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    {state₁ state₂ : ConcreteState Reg}
    (hRegs : state₁.regs = state₂.regs) (hMem : state₁.mem = state₂.mem) :
    state₁ = state₂ := by
  cases state₁
  cases state₂
  cases hRegs
  cases hMem
  rfl

abbrev TempEnv := Nat → UInt64

def TempEnv.empty : TempEnv := fun _ => 0

def TempEnv.write (temps : TempEnv) (tmp : Nat) (value : UInt64) : TempEnv :=
  fun tmp' => if tmp' = tmp then value else temps tmp'

@[simp] theorem TempEnv.write_same (temps : TempEnv) (tmp : Nat) (value : UInt64) :
    TempEnv.write temps tmp value tmp = value := by
  simp [TempEnv.write]

@[simp] theorem TempEnv.write_other (temps : TempEnv) {tmp tmp' : Nat} (value : UInt64)
    (h : tmp' ≠ tmp) : TempEnv.write temps tmp value tmp' = temps tmp' := by
  simp [TempEnv.write, h]

@[simp] def ConcreteState.read {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (reg : Reg) : UInt64 :=
  state.regs reg

@[simp] def ConcreteState.write {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (reg : Reg) (value : UInt64) : ConcreteState Reg :=
  { state with regs := fun reg' => if reg' = reg then value else state.regs reg' }

@[simp] theorem ConcreteState.read_write_same {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) (reg : Reg) (value : UInt64) :
    (state.write reg value).read reg = value := by
  simp [ConcreteState.write, ConcreteState.read]

@[simp] theorem ConcreteState.read_write_other {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (state : ConcreteState Reg) {reg reg' : Reg}
    (value : UInt64) (h : reg' ≠ reg) : (state.write reg value).read reg' = state.read reg' := by
  simp [ConcreteState.write, ConcreteState.read, h]

/-- Computable register enumeration for hashing. Finset.toList is noncomputable
    in Mathlib, so we provide a concrete list instead. -/
class EnumReg (Reg : Type) where
  allRegs : List Reg

/-! ## ByteMem read-after-write lemmas -/

theorem readByte_writeByte_same (mem : ByteMem) (addr : UInt64) (val : UInt8) :
    ByteMem.readByte (ByteMem.writeByte mem addr val) addr = val := by
  simp [ByteMem.writeByte, ByteMem.readByte]

theorem readByte_writeByte_ne (mem : ByteMem) (a b : UInt64) (val : UInt8) (h : a ≠ b) :
    ByteMem.readByte (ByteMem.writeByte mem a val) b = ByteMem.readByte mem b := by
  simp only [ByteMem.writeByte, ByteMem.readByte, Function.update]
  exact dif_neg (Ne.symm h)

theorem readByte_writeLEAux_nonoverlap
    (mem : ByteMem) (addr value : UInt64) (n : Nat) (b : UInt64)
    (h : ∀ i : Nat, i < n → addr + UInt64.ofNat i ≠ b) :
    ByteMem.readByte (ByteMem.writeLEAux mem addr value n) b =
    ByteMem.readByte mem b := by
  induction n generalizing mem with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMem.writeLEAux]
    have hk : addr + UInt64.ofNat k ≠ b := h k (Nat.lt_succ_of_le (Nat.le_refl k))
    rw [ih (ByteMem.writeByte mem (addr + UInt64.ofNat k) _)
        (fun i hi => h i (Nat.lt_of_lt_of_le hi (Nat.le_succ k)))]
    exact readByte_writeByte_ne mem _ b _ hk

theorem readLEAux_writeLEAux_nonoverlap
    (mem : ByteMem) (storeAddr value : UInt64) (storeN : Nat)
    (loadAddr : UInt64) (loadN : Nat)
    (h : ∀ (i j : Nat), i < storeN → j < loadN →
      storeAddr + UInt64.ofNat i ≠ loadAddr + UInt64.ofNat j) :
    ByteMem.readLEAux (ByteMem.writeLEAux mem storeAddr value storeN) loadAddr loadN =
    ByteMem.readLEAux mem loadAddr loadN := by
  induction loadN with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMem.readLEAux]
    have ih' := ih (fun i j hi hj => h i j hi (Nat.lt_of_lt_of_le hj (Nat.le_succ k)))
    have hk := readByte_writeLEAux_nonoverlap mem storeAddr value storeN
      (loadAddr + UInt64.ofNat k)
      (fun i hi => h i k hi (Nat.lt_succ_of_le (Nat.le_refl k)))
    rw [ih', hk]

/-! ## readLEAux after single writeByte at non-overlapping address -/

theorem readLEAux_writeByte_nonoverlap
    (mem : ByteMem) (a : UInt64) (val : UInt8)
    (b : UInt64) (n : Nat)
    (h : ∀ j : Nat, j < n → a ≠ b + UInt64.ofNat j) :
    ByteMem.readLEAux (ByteMem.writeByte mem a val) b n =
    ByteMem.readLEAux mem b n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMem.readLEAux]
    have hk : a ≠ b + UInt64.ofNat k := h k (Nat.lt_succ_of_le (Nat.le_refl k))
    have ih' := ih (fun j hj => h j (Nat.lt_of_lt_of_le hj (Nat.le_succ k)))
    rw [ih', readByte_writeByte_ne mem a (b + UInt64.ofNat k) val hk]

/-! ## Byte round-trip: read after write at same address

These theorems show that writing a value and reading it back at the same
address and width gives `truncate w v` (the value masked to width bits). -/

theorem read_write_same_w8 (M : ByteMem) (a v : UInt64) :
    ByteMem.read .w8 (ByteMem.write .w8 M a v) a = truncate .w8 v := by
  simp only [ByteMem.read, ByteMem.write, ByteMem.read8, ByteMem.write8]
  rw [readByte_writeByte_same]
  simp only [UInt64.ofNat, UInt8.ofNat, UInt8.toNat, UInt64.toNat,
    BitVec.ofNat_toNat, truncate, Width.mask]
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_ofNat]
  bv_decide

theorem read_write_same_w16 (M : ByteMem) (a v : UInt64) :
    ByteMem.read .w16 (ByteMem.write .w16 M a v) a = truncate .w16 v := by
  simp only [ByteMem.read, ByteMem.write, ByteMem.read16le, ByteMem.write16le,
    truncate, Width.mask]
  simp only [ByteMem.writeLEAux, ByteMem.readLEAux]
  rw [readByte_writeByte_same]
  have hne : a + UInt64.ofNat 0 ≠ a + UInt64.ofNat 1 := by simp
  rw [readByte_writeByte_ne _ _ _ _ hne, readByte_writeByte_same]
  simp only [UInt64.shiftLeft, UInt64.shiftRight, UInt64.mod,
    UInt64.ofNat, UInt8.ofNat, UInt8.toNat, UInt64.toNat,
    BitVec.ofNat_toNat]
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_ofNat]
  bv_decide

theorem read_write_same_w32 (M : ByteMem) (a v : UInt64) :
    ByteMem.read .w32 (ByteMem.write .w32 M a v) a = truncate .w32 v := by
  simp only [ByteMem.read, ByteMem.write, ByteMem.read32le, ByteMem.write32le,
             ByteMem.writeLEAux, ByteMem.readLEAux, truncate, Width.mask]
  repeat (first
    | rw [readByte_writeByte_same]
    | rw [readByte_writeByte_ne _ _ _ _ (by
        intro h; have := congrArg UInt64.toBitVec h; simp [UInt64.ofNat] at this)])
  show UInt64.ofBitVec _ = UInt64.ofBitVec _
  congr 1
  simp only [UInt64.ofNat, UInt8.ofNat, UInt8.toNat, UInt64.toNat,
             UInt64.shiftRight, UInt64.shiftLeft,
             UInt64.mod, BitVec.ofNat_toNat]
  bv_decide

theorem read_write_same_w64 (M : ByteMem) (a v : UInt64) :
    ByteMem.read .w64 (ByteMem.write .w64 M a v) a = truncate .w64 v := by
  simp only [ByteMem.read, ByteMem.write, ByteMem.read64le, ByteMem.write64le, truncate, Width.mask]
  simp only [ByteMem.writeLEAux, ByteMem.readLEAux]
  simp (discharger := simp) only [readByte_writeByte_same, readByte_writeByte_ne]
  -- Eliminate Nat round-trip: UInt64.ofNat (n % 256) → pure BitVec
  simp only [UInt8.toNat_ofNat', ← Nat.and_two_pow_sub_one_eq_mod]
  simp [UInt64.ofNat_toNat]
  rw [← UInt64.toBitVec_inj]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_and]
  unfold UInt64.shiftLeft UInt64.shiftRight
  simp [UInt64.mod]
  bv_decide

theorem ByteMem_read_write_same (w : Width) (M : ByteMem) (a v : UInt64) :
    ByteMem.read w (ByteMem.write w M a v) a = truncate w v := by
  cases w
  · exact read_write_same_w8 M a v
  · exact read_write_same_w16 M a v
  · exact read_write_same_w32 M a v
  · exact read_write_same_w64 M a v

/-! ## Write-write same address -/

theorem writeByte_writeByte_same (mem : ByteMem) (a : UInt64) (v1 v2 : UInt8) :
    ByteMem.writeByte (ByteMem.writeByte mem a v1) a v2 = ByteMem.writeByte mem a v2 := by
  exact ByteMem.eq_of_entries_eq (ByteMem.insertSorted_insertSorted_same mem.entries a v1 v2)

theorem writeByte_writeByte_comm (mem : ByteMem) (a b : UInt64) (va vb : UInt8) (h : a ≠ b) :
    ByteMem.writeByte (ByteMem.writeByte mem a va) b vb =
    ByteMem.writeByte (ByteMem.writeByte mem b vb) a va := by
  exact ByteMem.eq_of_entries_eq (ByteMem.insertSorted_insertSorted_comm mem.entries a b va vb h)

private theorem uint64_ofNat_injective {i k : Nat} (hi : i < UInt64.size) (hk : k < UInt64.size)
    (h : UInt64.ofNat i = UInt64.ofNat k) : i = k := by
  have h1 : (UInt64.ofNat i).toNat = i := Nat.mod_eq_of_lt hi
  have h2 : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt hk
  have := congrArg UInt64.toNat h
  omega

private theorem uint64_add_left_cancel' (R a b : UInt64) (h : R + a = R + b) : a = b := by
  have hbv : R.toBitVec + a.toBitVec = R.toBitVec + b.toBitVec := congrArg UInt64.toBitVec h
  have hab : a.toBitVec = b.toBitVec := by bv_omega
  exact congrArg UInt64.ofBitVec hab

private theorem writeByte_writeLEAux_comm (mem : ByteMem) (addr v : UInt64) (n : Nat)
    (a : UInt64) (va : UInt8) (ha : ∀ i, i < n → addr + UInt64.ofNat i ≠ a) :
    ByteMem.writeLEAux (ByteMem.writeByte mem a va) addr v n =
    ByteMem.writeByte (ByteMem.writeLEAux mem addr v n) a va := by
  induction n generalizing mem with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMem.writeLEAux]
    rw [writeByte_writeByte_comm _ a _ va _ (Ne.symm (ha k (Nat.lt_succ_of_le (Nat.le_refl k))))]
    exact ih _ (fun i hi => ha i (Nat.lt_succ_of_lt hi))

theorem writeLEAux_writeLEAux_same (mem : ByteMem) (addr v1 v2 : UInt64) (n : Nat) (hn : n ≤ UInt64.size) :
    ByteMem.writeLEAux (ByteMem.writeLEAux mem addr v1 n) addr v2 n =
    ByteMem.writeLEAux mem addr v2 n := by
  induction n generalizing mem with
  | zero => rfl
  | succ k ih =>
    simp only [ByteMem.writeLEAux]
    -- Commute writeByte(a+k, b2) past writeLEAux(a, v1, k):
    have hk_lt : k < UInt64.size := by omega
    have hne : ∀ i, i < k → addr + UInt64.ofNat i ≠ addr + UInt64.ofNat k := fun i hi heq => by
      have := uint64_add_left_cancel' addr _ _ heq
      have := uint64_ofNat_injective (by omega) hk_lt this
      omega
    rw [← writeByte_writeLEAux_comm _ addr v1 k _ _ hne, writeByte_writeByte_same]
    exact ih _ (by omega)

theorem ByteMem_write_write_same (w : Width) (M : ByteMem) (a v1 v2 : UInt64) :
    ByteMem.write w (ByteMem.write w M a v1) a v2 = ByteMem.write w M a v2 := by
  cases w <;> simp only [ByteMem.write, ByteMem.write8, ByteMem.write16le,
    ByteMem.write32le, ByteMem.write64le]
  · exact writeByte_writeByte_same M a _ _
  all_goals exact writeLEAux_writeLEAux_same M a v1 v2 _ (by simp [UInt64.size])

/-! ## Width-level non-overlap: read after write at non-overlapping byte ranges

The non-wrapping guards `h_a` and `h_b` ensure that the store and load byte ranges
don't wrap around the 2^64 address boundary, which is necessary for the interval
non-overlap condition to correctly imply pointwise address distinctness in UInt64
(modular) arithmetic. -/

private theorem uint64_add_ofNat_ne (a b : UInt64) (n m i j : Nat)
    (h_a : a.toNat + n ≤ UInt64.size) (h_b : b.toNat + m ≤ UInt64.size)
    (h : a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat)
    (hi : i < n) (hj : j < m) :
    a + UInt64.ofNat i ≠ b + UInt64.ofNat j := by
  -- Prove all Nat facts first, before UInt64 terms enter the context
  have h_ne : a.toNat + i ≠ b.toNat + j := by omega
  have h_i_lt : i < UInt64.size := by omega
  have h_j_lt : j < UInt64.size := by omega
  have h_ai_lt : a.toNat + i < UInt64.size := by omega
  have h_bj_lt : b.toNat + j < UInt64.size := by omega
  have h_lhs : (a + UInt64.ofNat i).toNat = a.toNat + i := by
    rw [UInt64.toNat_add]
    have : (UInt64.ofNat i).toNat = i := by
      simp [UInt64.ofNat, UInt64.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_i_lt]
    rw [this, Nat.mod_eq_of_lt h_ai_lt]
  have h_rhs : (b + UInt64.ofNat j).toNat = b.toNat + j := by
    rw [UInt64.toNat_add]
    have : (UInt64.ofNat j).toNat = j := by
      simp [UInt64.ofNat, UInt64.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_j_lt]
    rw [this, Nat.mod_eq_of_lt h_bj_lt]
  exact fun heq => h_ne (by rw [← h_lhs, ← h_rhs]; exact congrArg UInt64.toNat heq)

-- ═══════════════════════════════════════════════════════════════════════════
-- Footprints: byte ranges in the UInt64 address space
-- ═══════════════════════════════════════════════════════════════════════════

/-- A footprint is a contiguous byte range [addr, addr + size) in memory. -/
structure Footprint where
  addr : UInt64
  size : Nat
  deriving DecidableEq, Repr

/-- The footprint of a memory read or write at address `a` with width `w`. -/
def Footprint.ofWidth (a : UInt64) (w : Width) : Footprint :=
  ⟨a, w.byteCount⟩

/-- Two footprints are disjoint if no byte in one equals any byte in the other. -/
def Footprint.Disjoint (fp1 fp2 : Footprint) : Prop :=
  ∀ i j, i < fp1.size → j < fp2.size →
    fp1.addr + UInt64.ofNat i ≠ fp2.addr + UInt64.ofNat j

/-- Footprint disjointness is decidable (finite enumeration over bounded i, j). -/
instance Footprint.decidableDisjoint (fp1 fp2 : Footprint) : Decidable (Footprint.Disjoint fp1 fp2) :=
  -- Check all byte pairs: for each i < fp1.size and j < fp2.size,
  -- verify fp1.addr + i ≠ fp2.addr + j. UInt64 equality is decidable.
  if h : ∀ i : Fin fp1.size, ∀ j : Fin fp2.size,
      fp1.addr + UInt64.ofNat i.val ≠ fp2.addr + UInt64.ofNat j.val
  then isTrue fun i j hi hj => h ⟨i, hi⟩ ⟨j, hj⟩
  else isFalse fun hd => h (fun ⟨i, hi⟩ ⟨j, hj⟩ => hd i j hi hj)

/-- Read-write non-overlap with pointwise address distinctness precondition.
    This avoids .toNat range checks — each byte-pair inequality is decidable on UInt64 directly. -/
theorem ByteMem_read_write_ne (lw sw : Width) (M : ByteMem) (a v b : UInt64)
    (hp : ∀ i j, i < sw.byteCount → j < lw.byteCount → a + UInt64.ofNat i ≠ b + UInt64.ofNat j) :
    ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b := by
  cases lw <;> cases sw <;>
    simp only [ByteMem.read, ByteMem.write, Width.byteCount,
               ByteMem.read8, ByteMem.read16le, ByteMem.read32le, ByteMem.read64le,
               ByteMem.write8, ByteMem.write16le, ByteMem.write32le, ByteMem.write64le] at *
  all_goals first
    | exact readLEAux_writeLEAux_nonoverlap M a v _ b _ hp
    | (congr 1; congr 1
       exact readByte_writeLEAux_nonoverlap M a v _ b
        (fun i hi => by simpa using hp i 0 hi (by omega)))
    | exact readLEAux_writeByte_nonoverlap M a _ b _
        (fun j hj => by simpa using hp 0 j (by omega) hj)
    | (congr 1; congr 1
       exact readByte_writeByte_ne M a b _ (by simpa using hp 0 0 (by omega) (by omega)))

theorem ByteMem_read_write_nonoverlap (lw sw : Width) (M : ByteMem) (a v b : UInt64)
    (h_a : a.toNat + sw.byteCount ≤ UInt64.size)
    (h_b : b.toNat + lw.byteCount ≤ UInt64.size)
    (h : a.toNat + sw.byteCount ≤ b.toNat ∨ b.toNat + lw.byteCount ≤ a.toNat) :
    ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b := by
  have hp : ∀ i j, i < sw.byteCount → j < lw.byteCount →
      a + UInt64.ofNat i ≠ b + UInt64.ofNat j :=
    fun i j hi hj => uint64_add_ofNat_ne a b sw.byteCount lw.byteCount i j h_a h_b h hi hj
  cases lw <;> cases sw <;>
    simp only [ByteMem.read, ByteMem.write, Width.byteCount,
               ByteMem.read8, ByteMem.read16le, ByteMem.read32le, ByteMem.read64le,
               ByteMem.write8, ByteMem.write16le, ByteMem.write32le, ByteMem.write64le] at *
  all_goals first
    | exact readLEAux_writeLEAux_nonoverlap M a v _ b _ hp
    | (congr 1; congr 1
       exact readByte_writeLEAux_nonoverlap M a v _ b
        (fun i hi => by simpa using hp i 0 hi (by omega)))
    | exact readLEAux_writeByte_nonoverlap M a _ b _
        (fun j hj => by simpa using hp 0 j (by omega) hj)
    | (congr 1; congr 1
       exact readByte_writeByte_ne M a b _ (by simpa using hp 0 0 (by omega) (by omega)))

/-- Frame rule via footprint disjointness: if the write footprint is disjoint
    from the read footprint, the write doesn't affect the read. -/
theorem ByteMem_read_write_of_disjoint (lw sw : Width) (M : ByteMem) (a v b : UInt64)
    (h : Footprint.Disjoint (Footprint.ofWidth a sw) (Footprint.ofWidth b lw)) :
    ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b :=
  ByteMem_read_write_ne lw sw M a v b fun i j hi hj =>
    h i j (by simpa [Footprint.ofWidth] using hi) (by simpa [Footprint.ofWidth] using hj)

end VexISA
