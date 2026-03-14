/-!
# ElfSymbolTable — Minimal ELF64 symbol table reader

Reads an ELF64 little-endian binary to extract function symbols from
`.symtab`/`.strtab`. Pure byte-level parsing, no external dependencies.

Limitations:
- Little-endian only (rejects big-endian ELF with a clear error)
- Extended shnum (> 0xff00) not handled
- Symbol names assumed ASCII

Returns `Array (String × UInt64 × UInt64)` — (name, addr, size) for each
STT_FUNC symbol with nonzero size.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ElfSymbolTable

/-- Check that [off, off+len) is within data bounds. -/
private def checkBounds (data : ByteArray) (off : Nat) (len : Nat) (ctx : String) :
    Except String Unit :=
  if off + len > data.size then
    throw s!"Out of bounds reading {ctx} at offset {off} (need {len} bytes, file is {data.size})"
  else pure ()

/-- Read a little-endian UInt16 from a byte array at offset. -/
private def readU16LE (data : ByteArray) (off : Nat) : UInt16 :=
  let b0 := data.get! off |>.toUInt16
  let b1 := data.get! (off + 1) |>.toUInt16
  b0 ||| (b1 <<< 8)

/-- Read a little-endian UInt32 from a byte array at offset. -/
private def readU32LE (data : ByteArray) (off : Nat) : UInt32 :=
  let b0 := data.get! off |>.toUInt32
  let b1 := data.get! (off + 1) |>.toUInt32
  let b2 := data.get! (off + 2) |>.toUInt32
  let b3 := data.get! (off + 3) |>.toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

/-- Read a little-endian UInt64 from a byte array at offset. -/
private def readU64LE (data : ByteArray) (off : Nat) : UInt64 :=
  let lo := readU32LE data off |>.toUInt64
  let hi := readU32LE data (off + 4) |>.toUInt64
  lo ||| (hi <<< 32)

/-- Read a null-terminated string from a byte array at offset. -/
private def readCString (data : ByteArray) (off : Nat) : String := Id.run do
  let mut chars : Array Char := #[]
  let mut i := off
  while i < data.size do
    let b := data.get! i
    if b == 0 then break
    chars := chars.push (Char.ofNat b.toNat)
    i := i + 1
  return String.mk chars.toList

-- ELF64 constants
private def elfMagic : ByteArray := ⟨#[0x7f, 0x45, 0x4c, 0x46]⟩  -- \x7fELF
private def elfClass64 : UInt8 := 2
private def elfDataLSB : UInt8 := 1  -- little-endian
private def sht_SYMTAB : UInt32 := 2
private def stt_FUNC : UInt8 := 2

-- ELF64 header offsets
private def eiClass : Nat := 4
private def eiData : Nat := 5        -- e_ident[EI_DATA]: endianness
private def eShoff : Nat := 40       -- e_shoff: section header table offset
private def eShentsize : Nat := 58   -- e_shentsize: section header entry size
private def eShnum : Nat := 60       -- e_shnum: number of section headers

-- ELF64 section header offsets (within each shdr entry)
private def shType : Nat := 4        -- sh_type
private def shOffset : Nat := 24     -- sh_offset
private def shSize : Nat := 32       -- sh_size
private def shLink : Nat := 40       -- sh_link (for SYMTAB: index of associated STRTAB)
private def shEntsize : Nat := 56    -- sh_entsize

-- ELF64_Sym offsets (within each symbol entry, 24 bytes total)
private def stName : Nat := 0        -- st_name (4 bytes, index into strtab)
private def stInfo : Nat := 4        -- st_info (1 byte: type in low 4 bits)
private def stValue : Nat := 8       -- st_value (8 bytes, address)
private def stSize_ : Nat := 16      -- st_size (8 bytes)

/-- Read ELF64 symbol table from binary data.
    Returns (name, addr, size) for each STT_FUNC symbol with nonzero size. -/
def readSymbols (data : ByteArray) : Except String (Array (String × UInt64 × UInt64)) := do
  -- Validate ELF header (need at least 64 bytes)
  if data.size < 64 then throw "File too small for ELF64 header (need 64 bytes)"
  for i in [:4] do
    if data.get! i != elfMagic.get! i then
      throw "Not an ELF file (bad magic)"
  -- Validate ELF64
  if data.get! eiClass != elfClass64 then
    throw "Not an ELF64 file"
  -- Validate little-endian
  if data.get! eiData != elfDataLSB then
    throw "Not a little-endian ELF file (only LE supported)"
  -- Read section header table location
  let shoff := (readU64LE data eShoff).toNat
  let shentsize := (readU16LE data eShentsize).toNat
  let shnum := (readU16LE data eShnum).toNat
  if shoff == 0 || shnum == 0 then
    throw "No section header table"
  if shentsize < 64 then
    throw s!"Section header entry size too small: {shentsize} (need >= 64)"
  -- Validate section header table fits in file
  checkBounds data shoff (shnum * shentsize) "section header table"
  -- Find .symtab section
  let mut symtabIdx : Option Nat := none
  for i in [:shnum] do
    let shdrOff := shoff + i * shentsize
    let shtype := readU32LE data (shdrOff + shType)
    if shtype == sht_SYMTAB then
      symtabIdx := some i
      break
  let idx ← match symtabIdx with
    | some i => pure i
    | none => throw "No .symtab section found (stripped binary?)"
  -- Read .symtab section header
  let symtabShdr := shoff + idx * shentsize
  let symOffset := (readU64LE data (symtabShdr + shOffset)).toNat
  let symSize := (readU64LE data (symtabShdr + shSize)).toNat
  let symEntsize := (readU64LE data (symtabShdr + shEntsize)).toNat
  let strtabIdx := (readU32LE data (symtabShdr + shLink)).toNat
  if symEntsize == 0 then throw ".symtab has zero entry size"
  -- Validate .strtab section index
  if strtabIdx >= shnum then
    throw s!".symtab sh_link ({strtabIdx}) >= shnum ({shnum})"
  -- Validate symbol table data fits in file
  checkBounds data symOffset symSize "symbol table data"
  -- Read associated .strtab section header
  let strtabShdr := shoff + strtabIdx * shentsize
  checkBounds data strtabShdr shentsize "strtab section header"
  let strtabOffset := (readU64LE data (strtabShdr + shOffset)).toNat
  let strtabSize := (readU64LE data (strtabShdr + shSize)).toNat
  checkBounds data strtabOffset strtabSize "string table data"
  -- Parse symbol entries
  let numSyms := symSize / symEntsize
  let mut result : Array (String × UInt64 × UInt64) := #[]
  for i in [:numSyms] do
    let symOff := symOffset + i * symEntsize
    -- Each sym entry must be readable
    checkBounds data symOff symEntsize s!"symbol entry {i}"
    let info := data.get! (symOff + stInfo)
    let symType := info &&& 0x0f
    if symType != stt_FUNC then continue
    let size := readU64LE data (symOff + stSize_)
    if size == 0 then continue
    let nameIdx := (readU32LE data (symOff + stName)).toNat
    if strtabOffset + nameIdx >= data.size then
      throw s!"Symbol name index {nameIdx} out of string table bounds"
    let addr := readU64LE data (symOff + stValue)
    let name := readCString data (strtabOffset + nameIdx)
    result := result.push (name, addr, size)
  return result

/-- Read ELF64 symbol table from a file path.
    Returns (name, addr, size) for each STT_FUNC symbol with nonzero size. -/
def readSymbolsFromFile (path : System.FilePath) : IO (Array (String × UInt64 × UInt64)) := do
  let data ← IO.FS.readBinFile path
  match readSymbols data with
  | .ok syms => return syms
  | .error e => throw (IO.userError s!"ELF parse error in {path}: {e}")

end ElfSymbolTable
