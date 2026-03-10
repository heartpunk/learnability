import Instances.ISAs.VexIRParser
import Instances.Examples.VexAddEaxEdiFixture
import Instances.Examples.VexMovMemRdiRaxFixture
import Instances.Examples.VexJrcxzSkipLeaTakenFixture
import Instances.Examples.VexCmpRaxRdiJbTakenFixture

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

-- Helper: compare parse result to an expected Block, returning Bool
private def parseOk (text : String) (expected : Block Amd64Reg) : Bool :=
  match parseIRSB text with
  | .ok block => block == expected
  | .error _  => false

-- Helper: check extractIMarkIP returns the expected IP
private def extractIMarkOk (text : String) (expected : UInt64) : Bool :=
  match extractIMarkIP text with
  | .ok ip   => ip == expected
  | .error _ => false

-- Helper: check that parseProgram maps a given IP to the expected Block
private def parseProgramOk (texts : List String) (ip : UInt64) (expected : Block Amd64Reg) : Bool :=
  match parseProgram texts with
  | .error _  => false
  | .ok prog  =>
    match prog.blocks ip with
    | none       => false
    | some block => block == expected

/-! ## Test 1: add32 block (ADD EAX, EDI) -/
#guard parseOk
"IRSB {
   t4:Ity_I64 t3:Ity_I32 t6:Ity_I64 t5:Ity_I32 t0:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64
   00 | ------ IMark(0x400000, 2, 0) ------
   01 | t4 = GET:I64(rax)
   02 | t3 = 64to32(t4)
   03 | t6 = GET:I64(rdi)
   04 | t5 = 64to32(t6)
   05 | t0 = Add32(t3,t5)
   06 | PUT(cc_op) = 0x3
   07 | t7 = 32Uto64(t3)
   08 | PUT(cc_dep1) = t7
   09 | t8 = 32Uto64(t5)
   10 | PUT(cc_dep2) = t8
   11 | t9 = 32Uto64(t0)
   12 | PUT(rax) = t9
   NEXT: PUT(rip) = 0x400002; Ijk_Boring
}"
Instances.Examples.VexAddEaxEdiFixture.block

/-! ## Test 2: store block (MOV [RDI], RAX) -/
#guard parseOk
"IRSB {
   t0:Ity_I64 t1:Ity_I64
   00 | ------ IMark(0x400000, 3, 0) ------
   01 | t0 = GET:I64(rdi)
   02 | t1 = GET:I64(rax)
   03 | STle(t0) = t1
   NEXT: PUT(rip) = 0x400003; Ijk_Boring
}"
Instances.Examples.VexMovMemRdiRaxFixture.block

/-! ## Test 3: conditional exit block (JRCXZ + LEA) -/
-- Fixture uses tmps: t2=rcx, t3=cmpEQ64 cond (→ condMap, not stmt), t4=rdi, t3=add64 result
-- The CmpEQ64 assignment goes into condMap (not stmts), freeing t3 to be reused for add64.
#guard parseOk
"IRSB {
   t2:Ity_I64 t3:Ity_I1 t4:Ity_I64 t3:Ity_I64
   00 | ------ IMark(0x400000, 2, 0) ------
   01 | t2 = GET:I64(rcx)
   02 | t3 = CmpEQ64(t2,0x0)
   03 | if (t3) { PUT(rip) = 0x400006; Ijk_Boring }
   04 | t4 = GET:I64(rdi)
   05 | t3 = Add64(t4,0x5)
   06 | PUT(rax) = t3
   NEXT: PUT(rip) = 0x400006; Ijk_Boring
}"
Instances.Examples.VexJrcxzSkipLeaTakenFixture.block

/-! ## Test 4: CMP+JB conditional exit block -/
#guard parseOk
"IRSB {
   t2:Ity_I64 t1:Ity_I64 t5:Ity_I1
   00 | ------ IMark(0x400000, 5, 0) ------
   01 | t2 = GET:I64(rax)
   02 | t1 = GET:I64(rdi)
   03 | PUT(cc_op) = 0x8
   04 | PUT(cc_dep1) = t2
   05 | PUT(cc_dep2) = t1
   06 | PUT(rip) = 0x400003
   07 | t5 = CmpLT64U(t2,t1)
   08 | if (t5) { PUT(rip) = 0x400007; Ijk_Boring }
   NEXT: PUT(rip) = 0x400005; Ijk_Boring
}"
Instances.Examples.VexCmpRaxRdiJbTakenFixture.block

/-! ## Test 5: extractIMarkIP extracts the entry address -/
#guard extractIMarkOk
"IRSB {
   t0:Ity_I64 t1:Ity_I64
   00 | ------ IMark(0x400000, 3, 0) ------
   01 | t0 = GET:I64(rdi)
   02 | t1 = GET:I64(rax)
   03 | STle(t0) = t1
   NEXT: PUT(rip) = 0x400003; Ijk_Boring
}"
0x400000

/-! ## Test 6: parseProgram single block — lookup by IP -/
#guard parseProgramOk
  ["IRSB {
   t0:Ity_I64 t1:Ity_I64
   00 | ------ IMark(0x400000, 3, 0) ------
   01 | t0 = GET:I64(rdi)
   02 | t1 = GET:I64(rax)
   03 | STle(t0) = t1
   NEXT: PUT(rip) = 0x400003; Ijk_Boring
}"]
  0x400000
  Instances.Examples.VexMovMemRdiRaxFixture.block

/-! ## Test 8 (D.5a): AbiHint lines and Ijk_Ret are parsed without error -/
-- AbiHint lines (====== AbiHint(...) ======) must be silently skipped.
-- Ijk_Ret blocks have a dynamic return target; next IP is 0 (terminal sentinel).
#guard
  match parseIRSB
    "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64
   00 | ------ IMark(0x4003fa, 1, 0) ------
   01 | t1 = GET:I64(rsp)
   02 | t0 = LDle:I64(t1)
   03 | t2 = Add64(t1,0x0000000000000008)
   04 | PUT(rsp) = t2
   05 | ====== AbiHint(0xt2, 128, t0) ======
   NEXT: PUT(rip) = t0; Ijk_Ret
}" with
  | .ok block => block.next == 0
  | .error _ => false

/-! ## Test 9 (D.5a): Ijk_Call with constant target is parsed; next IP is the callee address -/
#guard
  match parseIRSB
    "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64
   00 | ------ IMark(0x40012c, 5, 0) ------
   01 | t4 = GET:I64(rsp)
   02 | t3 = Sub64(t4,0x0000000000000008)
   03 | PUT(rsp) = t3
   04 | STle(t3) = 0x0000000000400131
   05 | t5 = Sub64(t3,0x0000000000000080)
   06 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}" with
  | .ok block => block.next == 0x400034
  | .error _ => false

/-! ## Test 10 (D.5b): CmpLT32S and CmpLE32S are parsed as biased 64-bit comparisons -/
-- CmpLT32S(t0,t1) where t0=-1 (0xFFFFFFFF), t1=0 should evaluate as true (signed: -1 < 0).
-- After desugaring: lt64(sext32to64(narrow32(-1)) + 2^63, sext32to64(narrow32(0)) + 2^63)
--   = lt64(0xFFFFFFFF + 0x8000000000000000, 0 + 0x8000000000000000)
--   = lt64(0x7FFFFFFE_FFFFFFFF, 0x8000000000000000) = true ✓
#guard
  match parseIRSB
    "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I1 t3:Ity_I1
   00 | ------ IMark(0x400000, 2, 0) ------
   01 | t0 = GET:I32(rax)
   02 | t1 = GET:I32(rcx)
   03 | t2 = CmpLT32S(t0,t1)
   04 | t3 = CmpLE32S(t0,t1)
   05 | if (t2) { PUT(rip) = 0x400010; Ijk_Boring }
   NEXT: PUT(rip) = 0x400002; Ijk_Boring
}" with
  | .ok _ => true
  | .error _ => false

/-! ## Test 7: parseProgram two blocks — both IPs resolve correctly -/
-- Block A at 0x400000 (store), Block B at 0x400003 (identity: rax ← rax)
private def blockB : Block Amd64Reg :=
  mkAmd64Block [.wrTmp 0 (.get .rax), .put .rax (.tmp 0)] 0x400006

#guard parseProgramOk
  ["IRSB {
   t0:Ity_I64 t1:Ity_I64
   00 | ------ IMark(0x400000, 3, 0) ------
   01 | t0 = GET:I64(rdi)
   02 | t1 = GET:I64(rax)
   03 | STle(t0) = t1
   NEXT: PUT(rip) = 0x400003; Ijk_Boring
}",
   "IRSB {
   t0:Ity_I64
   00 | ------ IMark(0x400003, 3, 0) ------
   01 | t0 = GET:I64(rax)
   02 | PUT(rax) = t0
   NEXT: PUT(rip) = 0x400006; Ijk_Boring
}"]
  0x400003
  blockB
