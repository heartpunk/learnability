import Instances.ISAs.VexAmd64
import Instances.ISAs.VexProgram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA
namespace VexIRParser

/-! ## Compatibility helpers for Lean 4.28
    `String.trim`/`drop`/`dropRight` now return `String.Slice`, not `String`. -/

private abbrev myTrim (s : String) : String := s.trimAscii.toString

private def myDrop (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

private def myDropRight (s : String) (n : Nat) : String :=
  let chars := s.toList
  String.ofList (chars.take (chars.length - n))

/-! ## Parser state -/

structure ParseState where
  tempTypes : List (Nat × String)
  condMap   : List (Nat × Cond Amd64Reg)
  stmts     : List (Stmt Amd64Reg)

def ParseState.empty : ParseState := ⟨[], [], []⟩

def ParseState.lookupType (st : ParseState) (n : Nat) : Option String :=
  st.tempTypes.lookup n

def ParseState.lookupCond (st : ParseState) (n : Nat) : Option (Cond Amd64Reg) :=
  st.condMap.lookup n

def ParseState.addStmt (st : ParseState) (s : Stmt Amd64Reg) : ParseState :=
  { st with stmts := st.stmts ++ [s] }

def ParseState.addCond (st : ParseState) (n : Nat) (c : Cond Amd64Reg) : ParseState :=
  { st with condMap := (n, c) :: st.condMap }

/-! ## Lexical helpers -/

def resolveReg (s : String) : Except String Amd64Reg :=
  match myTrim s with
  | "rax" | "eax" | "ax" | "al" | "ah"  => .ok .rax
  | "rcx" | "ecx" | "cx" | "cl" | "ch"  => .ok .rcx
  | "rdx" | "edx" | "dx" | "dl" | "dh"  => .ok .rdx
  | "rsi" | "esi" | "si" | "sil"        => .ok .rsi
  | "rbp" | "ebp" | "bp" | "bpl"        => .ok .rbp
  | "rsp" | "esp" | "sp" | "spl"        => .ok .rsp
  | "rdi" | "edi" | "di" | "dil"        => .ok .rdi
  | "rip" | "eip"                        => .ok .rip
  | "cc_op"                              => .ok .cc_op
  | "cc_dep1"                            => .ok .cc_dep1
  | "cc_dep2"                            => .ok .cc_dep2
  | "cc_ndep"                            => .ok .cc_ndep
  | "r11" | "r11d" | "r11w" | "r11b"    => .ok .r11
  | "rbx" | "ebx" | "bx" | "bl" | "bh"  => .ok .rbx
  | "r8"  | "r8d" | "r8w" | "r8b"       => .ok .r8
  | "r9"  | "r9d" | "r9w" | "r9b"       => .ok .r9
  | "r12" | "r12d" | "r12w" | "r12b"    => .ok .r12
  -- r10, r13-r15: map to r12 (imprecise but allows parsing)
  | "r10" | "r10d" | "r10w" | "r10b"    => .ok .r12
  | "r13" | "r13d" | "r13w" | "r13b"    => .ok .r12
  | "r14" | "r14d" | "r14w" | "r14b"    => .ok .r12
  | "r15" | "r15d" | "r15w" | "r15b"    => .ok .r12
  | "fs"  | "fs_base"                   => .ok .fs_base
  | "xmm0" | "xmm0lq"                  => .ok .xmm0
  -- SSE registers (and sub-register variants): map all to xmm0
  -- since we model float/SIMD ops as opaque
  | "xmm1" | "xmm1lq" | "xmm2" | "xmm2lq"
  | "xmm3" | "xmm3lq" | "xmm4" | "xmm4lq"
  | "xmm5" | "xmm5lq" | "xmm6" | "xmm6lq"
  | "xmm7" | "xmm7lq" | "xmm8" | "xmm8lq"
  | "xmm9" | "xmm9lq" | "xmm10" | "xmm10lq"
  | "xmm11" | "xmm11lq" | "xmm12" | "xmm12lq"
  | "xmm13" | "xmm13lq" | "xmm14" | "xmm14lq"
  | "xmm15" | "xmm15lq"                => .ok .xmm0
  -- SSE rounding mode: map to xmm0 (opaque)
  | "sseround"                          => .ok .xmm0
  | r => .error s!"unknown register: {r}"

def typeToWidth (ty : String) : Except String Width :=
  match myTrim ty with
  | "I8"  | "Ity_I8"  => .ok .w8
  | "I16" | "Ity_I16" => .ok .w16
  | "I32" | "Ity_I32" | "F32" | "Ity_F32" => .ok .w32
  | "I64" | "Ity_I64" | "F64" | "Ity_F64" => .ok .w64
  | "V128" | "Ity_V128" => .ok .w64  -- 128-bit SIMD: treat as 64-bit (low half)
  | t => .error s!"unknown VEX type: {t}"

def parseHexStr (s : String) : Option Nat :=
  s.foldl (fun acc c =>
    acc.bind fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 16 + (c.toNat - '0'.toNat))
      else if 'a' ≤ c && c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10))
      else if 'A' ≤ c && c ≤ 'F' then some (n * 16 + (c.toNat - 'A'.toNat + 10))
      else none) (some 0)

def parseDecStr (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.foldl (fun acc c =>
    acc.bind fun n =>
      if '0' ≤ c && c ≤ '9' then some (n * 10 + (c.toNat - '0'.toNat))
      else none) (some 0)

def parseNumLit (s : String) : Option Nat :=
  let s := myTrim s
  if s.startsWith "0x" || s.startsWith "0X" then parseHexStr (myDrop s 2)
  else parseDecStr s

/-- Return `some n` iff `s` is exactly a tmp reference like "t0", "t42". -/
def parseTmpRef (s : String) : Option Nat :=
  if s.startsWith "t" && s.length > 1 then
    let digits := myDrop s 1
    if digits.all (·.isDigit) then parseDecStr digits else none
  else none

/-! ## String structure helpers (List Char based to avoid String.Pos changes) -/

/-- Split "Op(a,b)" → ("Op", "a,b"), handling nested parens. -/
def splitOp (s : String) : Option (String × String) :=
  match s.splitOn "(" with
  | [] | [_] => none
  | opPart :: rest =>
    let inner := String.intercalate "(" rest
    if inner.endsWith ")" then some (opPart, myDropRight inner 1)
    else none

/-- Split `s` at top-level commas (depth 0 w.r.t. parentheses). -/
private def splitTCChars
    (chars : List Char) (depth : Nat) (cur : List Char) (acc : List String)
    : List String :=
  match chars with
  | [] =>
    let seg := myTrim (String.ofList cur.reverse)
    acc ++ [seg]
  | c :: rest =>
    if c == ',' && depth == 0 then
      let seg := myTrim (String.ofList cur.reverse)
      splitTCChars rest 0 [] (acc ++ [seg])
    else if c == '(' then splitTCChars rest (depth + 1) (c :: cur) acc
    else if c == ')' && depth > 0 then splitTCChars rest (depth - 1) (c :: cur) acc
    else splitTCChars rest depth (c :: cur) acc

def splitTopCommas (s : String) : List String :=
  splitTCChars s.toList 0 [] []

/-- Find 0-based char index of matching close-paren, given `depth` opens already consumed. -/
private def findCloseIdx (chars : List Char) (depth : Nat) (idx : Nat) : Option Nat :=
  match chars with
  | [] => none
  | c :: rest =>
    if c == ')' then
      if depth == 1 then some idx
      else findCloseIdx rest (depth - 1) (idx + 1)
    else if c == '(' then findCloseIdx rest (depth + 1) (idx + 1)
    else findCloseIdx rest depth (idx + 1)

/-! ## Expression parser -/

def inferStoreWidth (valueStr : String) (st : ParseState) : Except String Width :=
  match parseTmpRef (myTrim valueStr) with
  | some n =>
    match st.lookupType n with
    | some ty => typeToWidth ty
    | none    => .error s!"no type declaration for t{n}"
  | none => .ok .w64

def parseExpr (s : String) (st : ParseState) (fuel : Nat := s.length + 1)
    : Except String (Expr Amd64Reg) :=
  match fuel with
  | 0 => .error s!"parseExpr: recursion limit exceeded on: {s}"
  | fuel + 1 =>
  let s := myTrim s
  -- Bug fix 2: strip VEX type annotation suffix (e.g. ":Ity_I64" on CCall results)
  let s := (s.splitOn ":Ity_").headI
  match parseTmpRef s with
  | some n => .ok (.tmp n)
  | none =>
  if s.startsWith "0x" || s.startsWith "0X" then
    match parseHexStr (myDrop s 2) with
    | some n => .ok (.const (UInt64.ofNat n))
    | none   => .error s!"bad hex constant: {s}"
  else
    -- Bug fix 1: try splitOp BEFORE the digit-prefix check so that digit-prefixed
    -- cast operators like "64to32(t4)", "32Uto64(t0)", "8Uto32(t1)" are not
    -- mistakenly parsed as decimal literals.
    match splitOp s with
    | none =>
      -- No parentheses: must be a bare decimal constant (e.g. "0", "3").
      -- parseDecStr returns none for strings with non-digit chars.
      match parseDecStr s with
      | some n => .ok (.const (UInt64.ofNat n))
      | none   => .error s!"cannot parse expression: {s}"
    | some (op, argsStr) =>
      if op.startsWith "GET:" then
        resolveReg argsStr |>.map .get
      else if op.startsWith "LDle:" then do
        let w    ← typeToWidth (myDrop op 5)
        let addr ← parseExpr argsStr st fuel
        .ok (.load w addr)
      else
        let args := splitTopCommas argsStr
        match op, args with
        | "64to32",  [a] => do let e ← parseExpr a st fuel; .ok (.narrow32 e)
        | "32Uto64", [a] => do let e ← parseExpr a st fuel; .ok (.zext64 e)
        | "DivModS64to32", [a, b] => do
          -- Signed div+mod packed into 64 bits. No symbolic div op, so approximate
          -- as the dividend (preserves dataflow for grammar extraction).
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "32HLto64", [hi, lo] => do
          let h ← parseExpr hi st fuel; let l ← parseExpr lo st fuel
          .ok (.or64 (.shl64 (.zext64 (.narrow32 h)) (.const 32)) (.zext64 (.narrow32 l)))
        | "8Sto32",  [a] => do let e ← parseExpr a st fuel; .ok (.sext8to32 e)
        | "32Sto64", [a] => do let e ← parseExpr a st fuel; .ok (.sext32to64 e)
        | "8Uto32",  [a] => parseExpr a st fuel
        | "8Uto64",  [a] => parseExpr a st fuel
        | "16Uto32", [a] => parseExpr a st fuel
        | "16Uto64", [a] => parseExpr a st fuel
        | "64to8",   [a] => do let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFF))
        | "64to16",  [a] => do let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFFFF))
        | "8Sto64",  [a] => do let e ← parseExpr a st fuel; .ok (.sext32to64 (.sext8to32 e))
        | "1Uto8",   [a] => parseExpr a st fuel
        | "1Uto64",  [a] => parseExpr a st fuel
        | "64to1",   [a] => parseExpr a st fuel
        | "1Uto32",  [a] => parseExpr a st fuel
        | "32to1",   [a] => parseExpr a st fuel
        | "Add32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.add32 l r)
        | "Sub32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.sub32 l r)
        | "Shl32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.shl32 l r)
        | "And32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.and32 l r)
        | "Or32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.or32 l r)
        | "Xor32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.xor32 l r)
        | "Sar64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.sar64 l r)
        | "Sar32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.sar32 l r)
        | "ITE", [cond, t, f] => do
          let c ← parseExpr cond st fuel; let tv ← parseExpr t st fuel; let fv ← parseExpr f st fuel
          .ok (.ite c tv fv)
        | "Not32", [a] => do
          let e ← parseExpr a st fuel; .ok (.not32 e)
        | "Not64", [a] => do
          let e ← parseExpr a st fuel; .ok (.not64 e)
        | "64HLto128", [hi, lo] => do
          -- Combine two 64-bit values into 128-bit. Model as low 64 bits only.
          let _ ← parseExpr hi st fuel; let l ← parseExpr lo st fuel; .ok l
        | "64UtoV128", [a] => do
          -- Zero-extend 64-bit to 128-bit SIMD vector. We only model the low 64 bits.
          let e ← parseExpr a st fuel; .ok e
        | "64HIto32", [a] => do
          -- High 32 bits of a 64-bit value.
          let e ← parseExpr a st fuel; .ok (.narrow32 (.shr64 e (.const 32)))
        | "MullU64", [a, b] => do
          -- High 64 bits of unsigned 128-bit product. Used for div-by-constant optimization.
          -- No SymExpr constructor — approximate as opaque (return first operand).
          -- Correct implementation would need 128-bit arithmetic.
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "MullU8", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel
          .ok (.mul64 (.and64 l (.const 0xFF)) (.and64 r (.const 0xFF)))
        | "Mul32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.mul32 l r)
        | "Mul64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.mul64 l r)
        | "Or8",  [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.or64 l r)
        | "And8", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.and64 l r)
        | "Sub8", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.sub64 l r)
        | "Add64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.add64 l r)
        | "Sub64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.sub64 l r)
        | "Xor64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.xor64 l r)
        | "And64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.and64 l r)
        | "Or64",  [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.or64  l r)
        | "Shl64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.shl64 l r)
        | "Shr64", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.shr64 l r)
        | "128HIto64", [a] => do
          -- High 64 bits of a 128-bit value. We model 128-bit as low 64 only,
          -- so approximate high half as 0.
          let _ ← parseExpr a st fuel; .ok (.const 0)
        | "128to64", [a] => do
          -- Low 64 bits of 128-bit value — identity in our model.
          let e ← parseExpr a st fuel; .ok e
        | "V128to64", [a] => do
          -- Low 64 bits of 128-bit SIMD vector — identity in our model.
          let e ← parseExpr a st fuel; .ok e
        | "V128HIto64", [a] => do
          -- High 64 bits of 128-bit SIMD vector. Approximate as 0.
          let _ ← parseExpr a st fuel; .ok (.const 0)
        | "DivModS128to64", [a, b] => do
          -- 128-bit signed division producing quotient:remainder packed in 128 bits.
          -- Approximate as the low 64 bits of the dividend (dataflow preservation).
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "DivModU128to64", [a, b] => do
          -- Unsigned variant of the above.
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        -- Floating-point / SSE operations: model as opaque (return const 0 or
        -- pass through integer bits). These don't affect control flow in typical
        -- parser code, so opaque representation is sufficient for grammar extraction.
        | "I64StoF64", [_, a] => do
          -- Int-to-float conversion. Pass through the integer value.
          let e ← parseExpr a st fuel; .ok e
        | "I64StoF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "I64UtoF64", [_, a] => do
          let e ← parseExpr a st fuel; .ok e
        | "I64UtoF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "I32StoF64", [_, a] => do
          let e ← parseExpr a st fuel; .ok e
        | "I32StoF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "I32UtoF64", [_, a] => do
          let e ← parseExpr a st fuel; .ok e
        | "I32UtoF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "F64toI64S", [_, a] | "F64toI64S", [a] => do
          -- Float-to-int conversion. Pass through as opaque.
          let e ← parseExpr a st fuel; .ok e
        | "F64toI64U", [_, a] | "F64toI64U", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "F64toI32S", [_, a] | "F64toI32S", [a] => do
          let e ← parseExpr a st fuel; .ok (.narrow32 e)
        | "F64toI32U", [_, a] | "F64toI32U", [a] => do
          let e ← parseExpr a st fuel; .ok (.narrow32 e)
        | "F64toF32", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "F32toF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "AddF64", [_, a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "SubF64", [_, a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "MulF64", [_, a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "DivF64", [_, a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "NegF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "AbsF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "SqrtF64", [_, a] => do
          let e ← parseExpr a st fuel; .ok e
        | "CmpF64", [_, a, b] => do
          -- Float comparison returning integer flags. Approximate as 0 (unordered).
          let _ ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok (.const 0)
        | "CmpF64", [a, b] => do
          -- 2-arg form of float comparison.
          let _ ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok (.const 0)
        | "ReinterpF64asI64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "ReinterpI64asF64", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "ReinterpF32asI32", [a] => do
          let e ← parseExpr a st fuel; .ok (.narrow32 e)
        | "ReinterpI32asF32", [a] => do
          let e ← parseExpr a st fuel; .ok e
        | "Shr32", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel
          .ok (.narrow32 (.shr64 (.zext64 (.narrow32 l)) r))
        -- 128-bit SIMD vector operations: model as low 64 bits of first operand
        | "XorV128", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.xor64 l r)
        | "AndV128", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.and64 l r)
        | "OrV128", [a, b] => do
          let l ← parseExpr a st fuel; let r ← parseExpr b st fuel; .ok (.or64 l r)
        | "NotV128", [a] => do
          let e ← parseExpr a st fuel; .ok (.not64 e)
        | "Add64Fx2", [a, b] | "Add64F0x2", [a, b] => do
          -- SIMD double add (2x f64). Pass through first operand.
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "Sub64Fx2", [a, b] | "Sub64F0x2", [a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "Mul64Fx2", [a, b] | "Mul64F0x2", [a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "Div64Fx2", [a, b] | "Div64F0x2", [a, b] => do
          let l ← parseExpr a st fuel; let _ ← parseExpr b st fuel; .ok l
        | "SetV128lo64", [a, b] => do
          -- Set the low 64 bits of a V128 to the given value.
          let _ ← parseExpr a st fuel; let e ← parseExpr b st fuel; .ok e
        | "16to8",  [a] => do
          let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFF))
        | "32to8",  [a] => do
          let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFF))
        | "32to16", [a] => do
          let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFFFF))
        | "16Sto32", [a] => do
          -- Sign-extend 16 to 32: approximate as zero-extend
          let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFFFF))
        | "16Sto64", [a] => do
          let e ← parseExpr a st fuel; .ok (.and64 e (.const 0xFFFF))
        | "amd64g_calculate_condition", [codeStr, opStr, dep1Str, dep2Str, _ndepStr] => do
          -- Condition flag calculation used as expression value (0 or 1).
          -- Lower directly to ite(condition, 1, 0) without going through Cond type.
          let code ← match parseNumLit codeStr with
            | some n => .ok (UInt64.ofNat n)
            | none   => .error s!"bad CCall code: {codeStr}"
          let ccOp   ← parseExpr opStr   st fuel
          let ccDep1 ← parseExpr dep1Str st fuel
          let ccDep2 ← parseExpr dep2Str st fuel
          -- Code 0x4 = zero flag: result is 1 if dep1 - dep2 == 0
          -- Other codes: conservatively return 0
          if code = 0x4 then
            .ok (.ite (.sub64 (.low32 ccDep1) (.low32 ccDep2)) (.const 0) (.const 1))
          else
            -- Unsupported condition code — return 0 (conservative)
            .ok (.const 0)
        | _, _ => .error s!"unsupported expression: {s}"

/-! ## Condition parser -/

def parseCond (op : String) (argsStr : String) (st : ParseState)
    : Except String (Cond Amd64Reg) :=
  let args := splitTopCommas argsStr
  match op, args with
  | "CmpEQ64",  [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st; .ok (.eq64 l r)
  | "CmpLT64U", [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st; .ok (.lt64 l r)
  | "CmpLE64U", [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st; .ok (.le64 l r)
  | "CmpEQ8",   [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.eq64 (.and64 l (.const 0xFF)) (.and64 r (.const 0xFF)))
  | "CmpEQ16",  [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.eq64 (.and64 l (.const 0xFFFF)) (.and64 r (.const 0xFFFF)))
  | "CmpEQ32",  [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.eq64 (.zext64 (.narrow32 l)) (.zext64 (.narrow32 r)))
  | "CmpLT32U", [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.lt64 (.zext64 (.narrow32 l)) (.zext64 (.narrow32 r)))
  | "CmpLE32U", [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.le64 (.zext64 (.narrow32 l)) (.zext64 (.narrow32 r)))
  | "CmpLT32S", [a, b] => do
    -- Signed 32-bit less-than: sign-extend both to 64 bits then bias by 2^63 for unsigned compare.
    let l ← parseExpr a st; let r ← parseExpr b st
    let bias : Expr Amd64Reg := .const 0x8000_0000_0000_0000
    .ok (.lt64 (.add64 (.sext32to64 (.narrow32 l)) bias) (.add64 (.sext32to64 (.narrow32 r)) bias))
  | "CmpLE32S", [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    let bias : Expr Amd64Reg := .const 0x8000_0000_0000_0000
    .ok (.le64 (.add64 (.sext32to64 (.narrow32 l)) bias) (.add64 (.sext32to64 (.narrow32 r)) bias))
  | "CmpNE64",  [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st; .ok (.ne64 l r)
  | "CmpNE32",  [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.ne64 (.zext64 (.narrow32 l)) (.zext64 (.narrow32 r)))
  | "CmpNE16",  [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.ne64 (.and64 l (.const 0xFFFF)) (.and64 r (.const 0xFFFF)))
  | "CmpNE8",   [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    .ok (.ne64 (.and64 l (.const 0xFF)) (.and64 r (.const 0xFF)))
  | "CmpLE64S", [a, b] => do
    -- Signed 64-bit LE: bias by 2^63 then unsigned compare (same pattern as CmpLT32S)
    let l ← parseExpr a st; let r ← parseExpr b st
    let bias : Expr Amd64Reg := .const 0x8000_0000_0000_0000
    .ok (.le64 (.add64 l bias) (.add64 r bias))
  | "CmpLT64S", [a, b] => do
    let l ← parseExpr a st; let r ← parseExpr b st
    let bias : Expr Amd64Reg := .const 0x8000_0000_0000_0000
    .ok (.lt64 (.add64 l bias) (.add64 r bias))
  | "amd64g_calculate_condition",
      [codeStr, opStr, dep1Str, dep2Str, ndepStr] => do
    let code ← match parseNumLit codeStr with
      | some n => .ok (UInt64.ofNat n)
      | none   => .error s!"bad CCall code: {codeStr}"
    let ccOp   ← parseExpr opStr   st
    let ccDep1 ← parseExpr dep1Str st
    let ccDep2 ← parseExpr dep2Str st
    let ccNdep ← parseExpr ndepStr st
    .ok (.amd64CalculateCondition code ccOp ccDep1 ccDep2 ccNdep)
  | _, _ => .error s!"unsupported condition: {op}({argsStr})"

private def isCondOp (op : String) : Bool :=
  op ∈ (["CmpEQ64", "CmpLT64U", "CmpLE64U", "CmpNE64", "CmpLE64S",
          "CmpEQ8", "CmpEQ16", "CmpEQ32", "CmpLT32U", "CmpLE32U", "CmpNE8", "CmpNE16", "CmpNE32",
          "CmpLT32S", "CmpLE32S", "CmpLT64S"] : List String)

private def isCondPropOp (op : String) : Bool :=
  op ∈ (["1Uto8", "1Uto64", "64to1", "1Uto32", "32to1"] : List String)

/-! ## Statement processing -/

def handleTmpAssign (tmpIdx : Nat) (rhs : String) (st : ParseState)
    : Except String ParseState := do
  let rhs := myTrim rhs
  if let some srcIdx := parseTmpRef rhs then
    return if let some c := st.lookupCond srcIdx then st.addCond tmpIdx c
           else st.addStmt (.wrTmp tmpIdx (.tmp srcIdx))
  match splitOp rhs with
  | none =>
    let expr ← parseExpr rhs st
    return st.addStmt (.wrTmp tmpIdx expr)
  | some (op, argsStr) =>
    if isCondOp op then
      let cond ← parseCond op argsStr st
      return st.addCond tmpIdx cond
    else if isCondPropOp op then
      let inner := myTrim (splitTopCommas argsStr).headI
      if let some innerIdx := parseTmpRef inner then
        if let some c := st.lookupCond innerIdx then
          return st.addCond tmpIdx c
      let expr ← parseExpr rhs st
      return st.addStmt (.wrTmp tmpIdx expr)
    else if op == "amd64g_calculate_condition" then
      -- Try to parse as condition. If the condition code is unsupported,
      -- still add to condMap (lowering will produce .not .true = always false)
      -- AND emit as expression via ite(cond, 1, 0) for use in value context.
      let cond ← parseCond op argsStr st
      return st.addCond tmpIdx cond
    else
      let expr ← parseExpr rhs st
      return st.addStmt (.wrTmp tmpIdx expr)

/-- Extract numeric target from "{ PUT(rip) = 0xHEX; Ijk_Boring }". -/
def extractExitTarget (body : String) : Except String UInt64 :=
  let body := myTrim (body.replace "{" "" |>.replace "}" "")
  match body.splitOn "=" with
  | _ :: rhs :: _ =>
    let addrStr := myTrim ((myTrim rhs).splitOn ";").headI
    match parseNumLit addrStr with
    | some n => .ok (UInt64.ofNat n)
    | none   => .error s!"bad exit target: {addrStr}"
  | _ => .error s!"bad exit body: {body}"

/-- Process one statement content string (after stripping "NN | " prefix). -/
def parseStmtContent (content : String) (st : ParseState) : Except String ParseState := do
  let content := myTrim content
  if content.isEmpty || content.startsWith "------" || content.startsWith "IMark"
      || content.startsWith "======" then
    return st
  if content.startsWith "if (" || content.startsWith "if(" then
    let afterIf := if content.startsWith "if (" then myDrop content 4 else myDrop content 3
    let chars := afterIf.toList
    match findCloseIdx chars 1 0 with
    | none => throw s!"unmatched parens in: {content}"
    | some closeIdx =>
      let guardStr   := myTrim (String.ofList (chars.take closeIdx))
      let afterParen := myTrim (String.ofList (chars.drop (closeIdx + 1)))
      let guardIdx ← match parseTmpRef guardStr with
        | some n => .ok n
        | none   => .error s!"expected tmp guard, got: {guardStr}"
      let cond ← match st.lookupCond guardIdx with
        | some c => .ok c
        | none   => .ok (.ne64 (.tmp guardIdx) (.const 0))  -- fallback: nonzero = true
      let target ← extractExitTarget afterParen
      return st.addStmt (.exit cond target)
  else if content.startsWith "PUT(" then
    let afterPut := myDrop content 4
    match afterPut.splitOn ")" with
    | [] => throw s!"bad PUT: {content}"
    | regStr :: rest =>
      let rhsStr := myTrim (String.intercalate ")" rest)
      let rhsStr := if rhsStr.startsWith "= " then myDrop rhsStr 2
                    else if rhsStr.startsWith "=" then myDrop rhsStr 1
                    else rhsStr
      let reg  ← resolveReg regStr
      let expr ← parseExpr (myTrim rhsStr) st
      return st.addStmt (.put reg expr)
  else if content.startsWith "STle(" then
    let afterSTle := myDrop content 5
    match afterSTle.splitOn ")" with
    | [] => throw s!"bad STle: {content}"
    | addrStr :: rest =>
      let rhsStr := myTrim (String.intercalate ")" rest)
      let rhsStr := if rhsStr.startsWith "= " then myDrop rhsStr 2
                    else if rhsStr.startsWith "=" then myDrop rhsStr 1
                    else myTrim rhsStr
      let width  ← inferStoreWidth rhsStr st
      let addr   ← parseExpr (myTrim addrStr) st
      let value  ← parseExpr rhsStr st
      return st.addStmt (.store width addr value)
  else if content.startsWith "t" then
    match content.splitOn " = " with
    | [lhs, rhs] =>
      let tmpIdx ← match parseTmpRef (myTrim lhs) with
        | some n => .ok n
        | none   => .error s!"bad tmp lhs: {lhs}"
      handleTmpAssign tmpIdx (myTrim rhs) st
    | _ => throw s!"cannot parse statement: {content}"
  else
    throw s!"unrecognized statement: {content}"

/-! ## Temp declaration line -/

def parseTempDecls (line : String) : List (Nat × String) :=
  (myTrim line).splitOn " " |>.filterMap fun part =>
    let part := myTrim part
    if part.isEmpty then none
    else match part.splitOn ":" with
      | [tmpStr, tyStr] =>
        match parseTmpRef tmpStr with
        | some n =>
          let ty := if tyStr.startsWith "Ity_" then myDrop tyStr 4 else tyStr
          some (n, ty)
        | none => none
      | _ => none

/-! ## NEXT line -/

def parseNextLine (line : String) : Except String UInt64 := do
  let rest := myTrim (if line.startsWith "NEXT:" then myDrop line 5 else line)
  -- Ijk_Ret: return address is dynamic (loaded from stack); use 0 as terminal sentinel.
  if rest.contains "Ijk_Ret" then return 0
  match rest.splitOn "=" with
  | _ :: rhs :: _ =>
    let addrStr := myTrim ((myTrim rhs).splitOn ";").headI
    match parseNumLit addrStr with
    | some n => .ok (UInt64.ofNat n)
    | none   =>
      -- Dynamic target (indirect branch or call via register/tmp): use 0 as sentinel.
      if parseTmpRef addrStr |>.isSome then return 0
      else .error s!"bad NEXT address: {addrStr}"
  | _ => .error s!"bad NEXT line: {line}"

/-! ## Top-level IRSB parser -/

private def stmtContent (line : String) : String :=
  match line.splitOn "|" with
  | [] | [_] => myTrim line
  | _ :: rest => myTrim (String.intercalate "|" rest)

/-- Parse the complete text output of `str(pyvex.IRSB(...))` into a `Block Amd64Reg`. -/
def parseIRSB (text : String) : Except String (Block Amd64Reg) := do
  let lines :=
    text.splitOn "\n"
    |>.map myTrim
    |>.filter fun l =>
      !l.isEmpty && l != "IRSB {" && l != "{" && l != "}" && !l.startsWith "IRSB"

  if lines.isEmpty then throw "empty IRSB"

  let (tempDecls, bodyLines) :=
    match lines with
    | first :: rest =>
      if first.startsWith "t" && first.contains ':' && !first.contains '|' then
        (parseTempDecls first, rest)
      else
        ([], lines)
    | [] => ([], [])

  let initSt : ParseState := { ParseState.empty with tempTypes := tempDecls }

  let (finalSt, maybeNext) ←
    bodyLines.foldlM (fun (acc : ParseState × Option UInt64) line => do
      let (st, nextIp) := acc
      let line := myTrim line
      if line.isEmpty then return (st, nextIp)
      else if line.startsWith "NEXT:" then do
        let rest := myTrim (myDrop line 5)
        if rest.contains "Ijk_Ret" then do
          -- Ijk_Ret: rip is loaded from the stack (a tmp variable).
          -- Parse "PUT(rip) = tN; Ijk_Ret" and emit `put rip (tmp N)` so the
          -- symbolic execution propagates the return-address load correctly.
          -- blockToCompTree_from sees next=0 and uses .skip (rip already set).
          match rest.splitOn "=" with
          | _ :: rhs :: _ =>
            let addrStr := myTrim ((myTrim rhs).splitOn ";").headI
            match parseTmpRef addrStr with
            | some n =>
              let st' := st.addStmt (.put .rip (.tmp n))
              return (st', some 0)
            | none => return (st, some 0)  -- no tmp ref; fall back to sentinel
          | _ => return (st, some 0)
        else do
          let ip ← parseNextLine line
          return (st, some ip)
      else do
        let st' ← parseStmtContent (stmtContent line) st
        return (st', nextIp))
    (initSt, (none : Option UInt64))

  match maybeNext with
  | none    => throw "no NEXT line found in IRSB"
  | some ip => .ok { stmts := finalSt.stmts, ip_reg := .rip, next := ip }

/-! ## Multi-block program parser -/

/-- Extract the entry IP from the first IMark line in a raw VEX IR text block.
    The IMark format is: `NN | ------ IMark(0xADDR, len, delta) ------` -/
def extractIMarkIP (text : String) : Except String UInt64 :=
  let lines := text.splitOn "\n" |>.map myTrim
  let hasIMark : String → Bool := fun l =>
    match l.splitOn "IMark(" with | [_] => false | _ => true
  match lines.find? hasIMark with
  | none => .error "no IMark found in IRSB"
  | some line =>
    match line.splitOn "IMark(" with
    | _ :: addrPart :: _ =>
      let addrStr := myTrim (addrPart.splitOn ",").headI
      match parseNumLit addrStr with
      | some n => .ok (UInt64.ofNat n)
      | none   => .error s!"bad IMark address: {addrStr}"
    | _ => .error s!"malformed IMark line: {line}"

/-- Parse a list of VEX IR text strings (one per IRSB) into a `Program Amd64Reg`.
    Each block's entry IP is extracted from its first IMark statement. -/
def parseProgram (irsbTexts : List String) : Except String (Program Amd64Reg) := do
  let pairs ← irsbTexts.mapM fun text => do
    let ip    ← extractIMarkIP text
    let block ← parseIRSB text
    return (ip, block)
  return { blocks := fun ip => (pairs.find? fun p => p.1 == ip).map (·.2) }

end VexIRParser
end VexISA
