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

private def ByteMem.readLEAux (mem : ByteMem) (addr : UInt64) : Nat → UInt64
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

private def ByteMem.writeLEAux (mem : ByteMem) (addr value : UInt64) : Nat → ByteMem
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

end VexISA
