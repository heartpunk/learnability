import Lean.Data.Json
import Instances.ISAs.VexAmd64
import Instances.ISAs.VexProgram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

open Lean (Json)

/-! ## JSON field helpers -/

private def getField (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

private def getString (j : Json) (key : String) : Except String String := do
  (← getField j key).getStr?

private def getNat (j : Json) (key : String) : Except String Nat := do
  let i ← (← getField j key).getInt?
  if i < 0 then .error s!"field '{key}' must be non-negative, got {i}"
  else .ok i.toNat

private def getUInt64 (j : Json) (key : String) : Except String UInt64 := do
  return UInt64.ofNat (← getNat j key)

private def getBinopArgs (j : Json) : Except String (Json × Json) := do
  let arr ← (← getField j "args").getArr?
  match arr with
  | #[l, r] => return (l, r)
  | _       => .error s!"Binop expects 2 args, got {arr.size}"

/-! ## AMD64 offset/type translation -/

def offsetToReg : Nat → Except String Amd64Reg
  | 16  => .ok .rax
  | 24  => .ok .rcx
  | 56  => .ok .rdi
  | 184 => .ok .rip
  | 144 => .ok .cc_op
  | 152 => .ok .cc_dep1
  | 160 => .ok .cc_dep2
  | 168 => .ok .cc_ndep
  | n   => .error s!"unknown AMD64 VEX guest state offset: {n}"

private def tyToWidth : String → Except String Width
  | "Ity_I8"  => .ok .w8
  | "Ity_I16" => .ok .w16
  | "Ity_I32" => .ok .w32
  | "Ity_I64" => .ok .w64
  | ty        => .error s!"unsupported VEX IR type: {ty}"

/-! ## Recursive parsers (mutually referential) -/

mutual

partial def parseExpr (j : Json) : Except String (Expr Amd64Reg) := do
  let tag ← getString j "tag"
  match tag with
  | "Const" =>
    return .const (← getUInt64 j "value")
  | "Get" =>
    return .get (← offsetToReg (← getNat j "offset"))
  | "RdTmp" =>
    return .tmp (← getNat j "tmp")
  | "Unop" => do
    let op  ← getString j "op"
    let arg ← parseExpr (← getField j "arg")
    match op with
    | "Iop_64to32"               => return .narrow32 arg
    | "Iop_32Uto64"              => return .zext64 arg
    | "Iop_8Sto32"               => return .sext8to32 arg
    | "Iop_8Uto32" | "Iop_8Uto64"
    | "Iop_16Uto32" | "Iop_16Uto64" => return arg
    | _                          => .error s!"unsupported Unop: {op}"
  | "Binop" => do
    let op       ← getString j "op"
    let (lJ, rJ) ← getBinopArgs j
    let l        ← parseExpr lJ
    let r        ← parseExpr rJ
    match op with
    | "Iop_Add64" => return .add64 l r
    | "Iop_Sub64" => return .sub64 l r
    | "Iop_And64" => return .and64 l r
    | "Iop_Or64"  => return .or64  l r
    | "Iop_Xor64" => return .xor64 l r
    | "Iop_Shl64" => return .shl64 l r
    | "Iop_Shr64" => return .shr64 l r
    | "Iop_Add32" => return .add32 l r
    | _           => .error s!"unsupported Binop for Expr: {op}"
  | "Load" => do
    let width ← tyToWidth (← getString j "ty")
    let addr  ← parseExpr (← getField j "addr")
    return .load width addr
  | _ => .error s!"unsupported Expr tag: {tag}"

partial def parseCond (j : Json) : Except String (Cond Amd64Reg) := do
  let tag ← getString j "tag"
  match tag with
  | "Binop" => do
    let op       ← getString j "op"
    let (lJ, rJ) ← getBinopArgs j
    let l        ← parseExpr lJ
    let r        ← parseExpr rJ
    match op with
    | "Iop_CmpEQ64"  => return .eq64 l r
    | "Iop_CmpLT64U" => return .lt64 l r
    | "Iop_CmpLE64U" => return .le64 l r
    | _              => .error s!"unsupported comparison op in Cond: {op}"
  | "CCall" => do
    let callee ← getString j "callee"
    if callee != "amd64g_calculate_condition" then
      .error s!"unsupported CCall helper: {callee}"
    else
      let arr ← (← getField j "args").getArr?
      match arr with
      | #[a0, a1, a2, a3, a4] => do
        let code ← parseExpr a0
        let codeVal ← match code with
          | .const n => .ok n
          | _        => .error "amd64CalculateCondition: condition code must be a constant Expr"
        return .amd64CalculateCondition codeVal
          (← parseExpr a1) (← parseExpr a2) (← parseExpr a3) (← parseExpr a4)
      | _ => .error s!"amd64g_calculate_condition expects 5 args, got {arr.size}"
  | _ => .error s!"unsupported Cond tag: {tag}"

partial def parseStmt (j : Json) : Except String (Stmt Amd64Reg) := do
  let tag ← getString j "tag"
  match tag with
  | "WrTmp" => do
    let n    ← getNat j "tmp"
    let expr ← parseExpr (← getField j "data")
    return .wrTmp n expr
  | "Put" => do
    let reg  ← offsetToReg (← getNat j "offset")
    let expr ← parseExpr (← getField j "data")
    return .put reg expr
  | "Store" => do
    let width ← tyToWidth (← getString j "ty")
    let addr  ← parseExpr (← getField j "addr")
    let value ← parseExpr (← getField j "data")
    return .store width addr value
  | "Exit" => do
    let cond   ← parseCond (← getField j "cond")
    let target ← getUInt64 j "target"
    return .exit cond target
  | _ => .error s!"unsupported Stmt tag: {tag}"

end

/-! ## Block and Program parsers -/

/--
Parse a raw VEX block JSON object `{"stmts":[...],"next":N}` into an `Amd64Block`.
The `ip_reg` is fixed to `.rip` for AMD64.
-/
def parseBlock (j : Json) : Except String (Block Amd64Reg) := do
  let arr   ← (← getField j "stmts").getArr?
  let stmts ← arr.toList.mapM parseStmt
  let next  ← getUInt64 j "next"
  return { stmts := stmts, ip_reg := .rip, next := next }

/--
Parse a raw VEX program JSON object `{"arch":"amd64","blocks":[{"ip":N,...},...]}` into
a `Program Amd64Reg`. Blocks are looked up by instruction pointer via linear search.
-/
def parseProgram (j : Json) : Except String (Program Amd64Reg) := do
  let arch ← getString j "arch"
  if arch != "amd64" then .error s!"unsupported arch: {arch}"
  let arr       ← (← getField j "blocks").getArr?
  let blockList ← arr.toList.mapM fun bj => do
    let ip    ← getUInt64 bj "ip"
    let block ← parseBlock bj
    return (ip, block)
  return { blocks := fun ip => (blockList.find? fun p => p.1 == ip).map (·.2) }

end VexISA
