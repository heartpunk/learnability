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
  | r => .error s!"unknown register: {r}"

def typeToWidth (ty : String) : Except String Width :=
  match myTrim ty with
  | "I8"  | "Ity_I8"  => .ok .w8
  | "I16" | "Ity_I16" => .ok .w16
  | "I32" | "Ity_I32" => .ok .w32
  | "I64" | "Ity_I64" => .ok .w64
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

partial def parseExpr (s : String) (st : ParseState) : Except String (Expr Amd64Reg) :=
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
        let addr ← parseExpr argsStr st
        .ok (.load w addr)
      else
        let args := splitTopCommas argsStr
        match op, args with
        | "64to32",  [a] => do let e ← parseExpr a st; .ok (.narrow32 e)
        | "32Uto64", [a] => do let e ← parseExpr a st; .ok (.zext64 e)
        | "8Sto32",  [a] => do let e ← parseExpr a st; .ok (.sext8to32 e)
        | "32Sto64", [a] => do let e ← parseExpr a st; .ok (.sext32to64 e)
        | "8Uto32",  [a] => parseExpr a st
        | "8Uto64",  [a] => parseExpr a st
        | "16Uto32", [a] => parseExpr a st
        | "16Uto64", [a] => parseExpr a st
        | "1Uto64",  [a] => parseExpr a st
        | "64to1",   [a] => parseExpr a st
        | "1Uto32",  [a] => parseExpr a st
        | "32to1",   [a] => parseExpr a st
        | "Add32", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.add32 l r)
        | "Sub32", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.sub32 l r)
        | "Shl32", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.shl32 l r)
        | "Add64", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.add64 l r)
        | "Sub64", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.sub64 l r)
        | "Xor64", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.xor64 l r)
        | "And64", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.and64 l r)
        | "Or64",  [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.or64  l r)
        | "Shl64", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.shl64 l r)
        | "Shr64", [a, b] => do
          let l ← parseExpr a st; let r ← parseExpr b st; .ok (.shr64 l r)
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
  op ∈ (["CmpEQ64", "CmpLT64U", "CmpLE64U",
          "CmpEQ32", "CmpLT32U", "CmpLE32U",
          "CmpLT32S", "CmpLE32S"] : List String)

private def isCondPropOp (op : String) : Bool :=
  op ∈ (["1Uto64", "64to1", "1Uto32", "32to1"] : List String)

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
        | none   => .error s!"no condition tracked for t{guardIdx}"
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
    | none   => .error s!"bad NEXT address: {addrStr}"
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
