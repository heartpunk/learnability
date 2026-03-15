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

abbrev ByteCell := UInt64 × UInt8
abbrev ByteMem := List ByteCell

def ByteMem.empty : ByteMem := []

def ByteMem.eraseAddr (mem : ByteMem) (addr : UInt64) : ByteMem :=
  mem.filter (fun cell => cell.1 ≠ addr)

@[simp] def ByteMem.readByte : ByteMem → UInt64 → UInt8
  | [], _ => 0
  | (cellAddr, value) :: rest, addr =>
      if cellAddr = addr then value else ByteMem.readByte rest addr

def ByteMem.writeByte (mem : ByteMem) (addr : UInt64) (value : UInt8) : ByteMem :=
  (addr, value) :: ByteMem.eraseAddr mem addr

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

/-- Erasing address `a` doesn't affect readByte at `b ≠ a`. -/
theorem readByte_eraseAddr_ne (mem : ByteMem) (a b : UInt64) (h : a ≠ b) :
    ByteMem.readByte (ByteMem.eraseAddr mem a) b =
    ByteMem.readByte mem b := by
  induction mem with
  | nil => rfl
  | cons cell rest ih =>
    simp only [ByteMem.eraseAddr, List.filter]
    by_cases hca : cell.1 = a
    · have : (cell.1 ≠ a) = False := by simp [hca]
      simp only [this, decide_false]
      simp only [ByteMem.readByte]
      have hcb : ¬(cell.1 = b) := fun hcb => h (hca ▸ hcb)
      simp only [hcb, ite_false]
      exact ih
    · have : (cell.1 ≠ a) = True := by simp [hca]
      simp only [this, decide_true]
      simp only [ByteMem.readByte]
      split
      · rfl
      · exact ih

theorem readByte_writeByte_same (mem : ByteMem) (addr : UInt64) (val : UInt8) :
    ByteMem.readByte (ByteMem.writeByte mem addr val) addr = val := by
  unfold ByteMem.writeByte; simp [ByteMem.readByte]

theorem readByte_writeByte_ne (mem : ByteMem) (a b : UInt64) (val : UInt8) (h : a ≠ b) :
    ByteMem.readByte (ByteMem.writeByte mem a val) b = ByteMem.readByte mem b := by
  unfold ByteMem.writeByte
  simp only [ByteMem.readByte, if_neg h]
  exact readByte_eraseAddr_ne mem a b h

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
  apply UInt64.ext
  simp [truncate, Width.mask]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact (Nat.and_two_pow_sub_one_eq_mod v.toNat 8).symm

theorem read_write_same_w16 (M : ByteMem) (a v : UInt64) :
    ByteMem.read .w16 (ByteMem.write .w16 M a v) a = truncate .w16 v := by
  sorry

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
  sorry

theorem ByteMem_read_write_same (w : Width) (M : ByteMem) (a v : UInt64) :
    ByteMem.read w (ByteMem.write w M a v) a = truncate w v := by
  cases w
  · exact read_write_same_w8 M a v
  · exact read_write_same_w16 M a v
  · exact read_write_same_w32 M a v
  · exact read_write_same_w64 M a v

/-! ## Width-level non-overlap: read after write at non-overlapping byte ranges -/

theorem ByteMem_read_write_nonoverlap (lw sw : Width) (M : ByteMem) (a v b : UInt64)
    (h : a + UInt64.ofNat sw.byteCount ≤ b ∨ b + UInt64.ofNat lw.byteCount ≤ a) :
    ByteMem.read lw (ByteMem.write sw M a v) b = ByteMem.read lw M b := by
  sorry

end VexISA
