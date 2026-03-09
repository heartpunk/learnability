import Instances.ISAs.VexDeserialize
import Instances.Examples.VexMovRaxMemRdiFixture
import Lean.Data.Json

/-!
Integration tests for `VexDeserialize`. Each test uses a hand-crafted raw pyvex JSON
string (PascalCase tags, numeric VEX guest-state offsets, Iop_ op names) and checks the
parsed result against known-correct values.
-/

open VexISA Lean

private def parseBlockStr (s : String) : Except String (Block Amd64Reg) :=
  match Json.parse s with
  | .error e => .error s!"JSON parse error: {e}"
  | .ok j    => parseBlock j

private def parsedEq (s : String) (expected : Block Amd64Reg) : Bool :=
  match parseBlockStr s with
  | .ok b    => b == expected
  | .error _ => false

private def parsedIsError (s : String) : Bool :=
  match parseBlockStr s with
  | .error _ => true
  | .ok _    => false

/-! ### mov rax, [rdi]
Raw pyvex for `48 8b 07`:
  t0 = GET:I64(offset=56)   -- rdi
  t1 = LDle:I64(t0)
  PUT(offset=16) = t1       -- rax
  NEXT = 0x400003 = 4194307
-/
#guard parsedEq
  "{\"stmts\":[\
    {\"tag\":\"WrTmp\",\"tmp\":0,\"data\":{\"tag\":\"Get\",\"offset\":56,\"ty\":\"Ity_I64\"}},\
    {\"tag\":\"WrTmp\",\"tmp\":1,\"data\":{\"tag\":\"Load\",\"ty\":\"Ity_I64\",\"addr\":{\"tag\":\"RdTmp\",\"tmp\":0}}},\
    {\"tag\":\"Put\",\"offset\":16,\"data\":{\"tag\":\"RdTmp\",\"tmp\":1}}\
  ],\"next\":4194307}"
  Instances.Examples.VexMovRaxMemRdiFixture.block

/-! ### Const and add64 -/
#guard parsedEq
  "{\"stmts\":[\
    {\"tag\":\"WrTmp\",\"tmp\":0,\"data\":{\"tag\":\"Binop\",\"op\":\"Iop_Add64\",\"args\":[\
      {\"tag\":\"Get\",\"offset\":24,\"ty\":\"Ity_I64\"},\
      {\"tag\":\"Const\",\"value\":5}]}}\
  ],\"next\":0}"
  (mkAmd64Block [.wrTmp 0 (.add64 (.get .rcx) (.const 5))] 0)

/-! ### 32-bit narrowing and zero-extension -/
#guard parsedEq
  "{\"stmts\":[\
    {\"tag\":\"WrTmp\",\"tmp\":0,\"data\":{\"tag\":\"Unop\",\"op\":\"Iop_64to32\",\
      \"arg\":{\"tag\":\"Get\",\"offset\":16,\"ty\":\"Ity_I64\"}}},\
    {\"tag\":\"WrTmp\",\"tmp\":1,\"data\":{\"tag\":\"Unop\",\"op\":\"Iop_32Uto64\",\
      \"arg\":{\"tag\":\"RdTmp\",\"tmp\":0}}}\
  ],\"next\":0}"
  (mkAmd64Block [.wrTmp 0 (.narrow32 (.get .rax)), .wrTmp 1 (.zext64 (.tmp 0))] 0)

/-! ### Store with w32 width -/
#guard parsedEq
  "{\"stmts\":[\
    {\"tag\":\"Store\",\"ty\":\"Ity_I32\",\
      \"addr\":{\"tag\":\"Get\",\"offset\":56,\"ty\":\"Ity_I64\"},\
      \"data\":{\"tag\":\"Get\",\"offset\":16,\"ty\":\"Ity_I64\"}}\
  ],\"next\":0}"
  (mkAmd64Block [.store .w32 (.get .rdi) (.get .rax)] 0)

/-! ### Error: unknown register offset -/
#guard parsedIsError
  "{\"stmts\":[{\"tag\":\"WrTmp\",\"tmp\":0,\
    \"data\":{\"tag\":\"Get\",\"offset\":99,\"ty\":\"Ity_I64\"}}],\"next\":0}"

/-! ### Error: unsupported Binop op -/
#guard parsedIsError
  "{\"stmts\":[{\"tag\":\"WrTmp\",\"tmp\":0,\
    \"data\":{\"tag\":\"Binop\",\"op\":\"Iop_Mul64\",\"args\":[\
      {\"tag\":\"Const\",\"value\":1},{\"tag\":\"Const\",\"value\":2}]}}],\"next\":0}"
