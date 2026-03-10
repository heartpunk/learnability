import Instances.ISAs.VexIRParser

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## Roundtrip test: all 60 next_sym blocks parse without error -/
-- Embedded from reference/tinyc/next_sym_cfg.json

private def nextSymBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x40006f, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t11 = GET:I64(rsp)
   03 | t10 = Sub64(t11,0x0000000000000008)
   04 | PUT(rsp) = t10
   05 | STle(t10) = t0
   06 | ------ IMark(0x400070, 3, 0) ------
   07 | PUT(rbp) = t10
   08 | ------ IMark(0x400073, 4, 0) ------
   09 | t2 = Sub64(t10,0x0000000000000010)
   10 | PUT(rsp) = t2
   11 | PUT(rip) = 0x0000000000400077
   12 | ------ IMark(0x400077, 7, 0) ------
   13 | t13 = LDle:I64(0x0000000000500028)
   14 | PUT(rip) = 0x000000000040007e
   15 | ------ IMark(0x40007e, 2, 0) ------
   16 | t15 = LDle:I32(t13)
   17 | t27 = 32Uto64(t15)
   18 | t14 = t27
   19 | PUT(rax) = t14
   20 | ------ IMark(0x400080, 3, 0) ------
   21 | t28 = 64to32(t14)
   22 | t16 = t28
   23 | PUT(cc_op) = 0x0000000000000007
   24 | t29 = 32Uto64(t16)
   25 | t18 = t29
   26 | PUT(cc_dep1) = t18
   27 | PUT(cc_dep2) = 0x000000000000007d
   28 | PUT(rip) = 0x0000000000400083
   29 | ------ IMark(0x400083, 6, 0) ------
   30 | t32 = 64to32(t18)
   31 | t33 = 64to32(0x000000000000007d)
   32 | t31 = CmpEQ32(t32,t33)
   33 | t30 = 1Uto64(t31)
   34 | t25 = t30
   35 | t34 = 64to1(t25)
   36 | t20 = t34
   37 | if (t20) { PUT(rip) = 0x400127; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400089; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I1 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I32 t15:Ity_I64 t16:Ity_I64 t17:Ity_I1 t18:Ity_I32 t19:Ity_I32 t20:Ity_I1

   00 | ------ IMark(0x400089, 3, 0) ------
   01 | t4 = GET:I64(rax)
   02 | t14 = 64to32(t4)
   03 | t3 = t14
   04 | PUT(cc_op) = 0x0000000000000007
   05 | t15 = 32Uto64(t3)
   06 | t5 = t15
   07 | PUT(cc_dep1) = t5
   08 | PUT(cc_dep2) = 0x000000000000007d
   09 | PUT(rip) = 0x000000000040008c
   10 | ------ IMark(0x40008c, 6, 0) ------
   11 | t18 = 64to32(t5)
   12 | t19 = 64to32(0x000000000000007d)
   13 | t17 = CmpLE32S(t18,t19)
   14 | t16 = 1Uto64(t17)
   15 | t12 = t16
   16 | t20 = 64to1(t12)
   17 | t7 = t20
   18 | if (t7) { PUT(rip) = 0x400092; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400207; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I1 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I32 t15:Ity_I64 t16:Ity_I64 t17:Ity_I1 t18:Ity_I32 t19:Ity_I32 t20:Ity_I1

   00 | ------ IMark(0x400092, 3, 0) ------
   01 | t4 = GET:I64(rax)
   02 | t14 = 64to32(t4)
   03 | t3 = t14
   04 | PUT(cc_op) = 0x0000000000000007
   05 | t15 = 32Uto64(t3)
   06 | t5 = t15
   07 | PUT(cc_dep1) = t5
   08 | PUT(cc_dep2) = 0x000000000000003d
   09 | PUT(rip) = 0x0000000000400095
   10 | ------ IMark(0x400095, 2, 0) ------
   11 | t18 = 64to32(t5)
   12 | t19 = 64to32(0x000000000000003d)
   13 | t17 = CmpLE32S(t18,t19)
   14 | t16 = 1Uto64(t17)
   15 | t12 = t16
   16 | t20 = 64to1(t12)
   17 | t7 = t20
   18 | if (t7) { PUT(rip) = 0x400097; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004000ce; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I1 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I32 t15:Ity_I64 t16:Ity_I64 t17:Ity_I1 t18:Ity_I32 t19:Ity_I32 t20:Ity_I1

   00 | ------ IMark(0x400097, 3, 0) ------
   01 | t4 = GET:I64(rax)
   02 | t14 = 64to32(t4)
   03 | t3 = t14
   04 | PUT(cc_op) = 0x0000000000000007
   05 | t15 = 32Uto64(t3)
   06 | t5 = t15
   07 | PUT(cc_dep1) = t5
   08 | PUT(cc_dep2) = 0x00000000ffffffff
   09 | PUT(rip) = 0x000000000040009a
   10 | ------ IMark(0x40009a, 6, 0) ------
   11 | t18 = 64to32(t5)
   12 | t19 = 64to32(0x00000000ffffffff)
   13 | t17 = CmpLT32S(t18,t19)
   14 | t16 = 1Uto64(t17)
   15 | t12 = t16
   16 | t20 = 64to1(t12)
   17 | t7 = t20
   18 | if (t7) { PUT(rip) = 0x400207; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004000a0; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I32 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I1 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I32 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I64 t27:Ity_I1 t28:Ity_I32 t29:Ity_I32 t30:Ity_I1

   00 | ------ IMark(0x4000a0, 3, 0) ------
   01 | t7 = GET:I64(rax)
   02 | t22 = 64to32(t7)
   03 | t6 = t22
   04 | t0 = Add32(t6,0x00000001)
   05 | t23 = 32Uto64(t0)
   06 | t10 = t23
   07 | PUT(rax) = t10
   08 | ------ IMark(0x4000a3, 3, 0) ------
   09 | t24 = 64to32(t10)
   10 | t11 = t24
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t25 = 32Uto64(t11)
   13 | t13 = t25
   14 | PUT(cc_dep1) = t13
   15 | PUT(cc_dep2) = 0x000000000000003e
   16 | PUT(rip) = 0x00000000004000a6
   17 | ------ IMark(0x4000a6, 6, 0) ------
   18 | t28 = 64to32(t13)
   19 | t29 = 64to32(0x000000000000003e)
   20 | t27 = CmpLE32U(t28,t29)
   21 | t26 = 1Uto64(t27)
   22 | t20 = t26
   23 | t30 = 64to1(t20)
   24 | t15 = t30
   25 | if (t15) { PUT(rip) = 0x4000ac; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400207; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I64 t9:Ity_I64 t10:Ity_I32 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I32 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I64

   00 | ------ IMark(0x4000ac, 2, 0) ------
   01 | t11 = GET:I64(rax)
   02 | t10 = 64to32(t11)
   03 | t9 = 32Uto64(t10)
   04 | ------ IMark(0x4000ae, 8, 0) ------
   05 | t13 = Shl64(t9,0x02)
   06 | ------ IMark(0x4000b6, 7, 0) ------
   07 | PUT(rip) = 0x00000000004000bd
   08 | ------ IMark(0x4000bd, 3, 0) ------
   09 | t15 = Add64(t13,0x00000000004016e8)
   10 | t20 = LDle:I32(t15)
   11 | t19 = 32Uto64(t20)
   12 | ------ IMark(0x4000c0, 2, 0) ------
   13 | t22 = 64to32(t19)
   14 | t21 = 32Sto64(t22)
   15 | ------ IMark(0x4000c2, 7, 0) ------
   16 | PUT(rdx) = 0x00000000004016e8
   17 | ------ IMark(0x4000c9, 3, 0) ------
   18 | t4 = Add64(t21,0x00000000004016e8)
   19 | PUT(cc_op) = 0x0000000000000004
   20 | PUT(cc_dep1) = t21
   21 | PUT(cc_dep2) = 0x00000000004016e8
   22 | PUT(rax) = t4
   23 | ------ IMark(0x4000cc, 2, 0) ------
   NEXT: PUT(rip) = t4; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I1 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I32 t15:Ity_I64 t16:Ity_I64 t17:Ity_I1 t18:Ity_I32 t19:Ity_I32 t20:Ity_I1

   00 | ------ IMark(0x4000ce, 3, 0) ------
   01 | t4 = GET:I64(rax)
   02 | t14 = 64to32(t4)
   03 | t3 = t14
   04 | PUT(cc_op) = 0x0000000000000007
   05 | t15 = 32Uto64(t3)
   06 | t5 = t15
   07 | PUT(cc_dep1) = t5
   08 | PUT(cc_dep2) = 0x000000000000007b
   09 | PUT(rip) = 0x00000000004000d1
   10 | ------ IMark(0x4000d1, 2, 0) ------
   11 | t18 = 64to32(t5)
   12 | t19 = 64to32(0x000000000000007b)
   13 | t17 = CmpEQ32(t18,t19)
   14 | t16 = 1Uto64(t17)
   15 | t12 = t16
   16 | t20 = 64to1(t12)
   17 | t7 = t20
   18 | if (t7) { PUT(rip) = 0x40010b; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004000d3; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4000d3, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400207; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4000d8, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004000dd
   03 | ------ IMark(0x4000dd, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004000e2
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4000e2, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ea; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4000e7, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x00000000004000ee
   04 | ------ IMark(0x4000ee, 6, 0) ------
   05 | STle(t2) = 0x0000000f
   06 | ------ IMark(0x4000f4, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4000f9, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x0000000000400100
   04 | ------ IMark(0x400100, 6, 0) ------
   05 | STle(t2) = 0x0000000f
   06 | ------ IMark(0x400106, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40010b, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400110
   03 | ------ IMark(0x400110, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400115
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x400115, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x000000000040011c
   04 | ------ IMark(0x40011c, 6, 0) ------
   05 | STle(t2) = 0x00000004
   06 | ------ IMark(0x400122, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400127, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040012c
   03 | ------ IMark(0x40012c, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400131
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x400131, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x0000000000400138
   04 | ------ IMark(0x400138, 6, 0) ------
   05 | STle(t2) = 0x00000005
   06 | ------ IMark(0x40013e, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400143, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400148
   03 | ------ IMark(0x400148, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x000000000040014d
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x40014d, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x0000000000400154
   04 | ------ IMark(0x400154, 6, 0) ------
   05 | STle(t2) = 0x00000006
   06 | ------ IMark(0x40015a, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40015f, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400164
   03 | ------ IMark(0x400164, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400169
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x400169, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x0000000000400170
   04 | ------ IMark(0x400170, 6, 0) ------
   05 | STle(t2) = 0x00000007
   06 | ------ IMark(0x400176, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40017b, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400180
   03 | ------ IMark(0x400180, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400185
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x400185, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x000000000040018c
   04 | ------ IMark(0x40018c, 6, 0) ------
   05 | STle(t2) = 0x00000008
   06 | ------ IMark(0x400192, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400197, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040019c
   03 | ------ IMark(0x40019c, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004001a1
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4001a1, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x00000000004001a8
   04 | ------ IMark(0x4001a8, 6, 0) ------
   05 | STle(t2) = 0x00000009
   06 | ------ IMark(0x4001ae, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4001b3, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004001b8
   03 | ------ IMark(0x4001b8, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004001bd
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4001bd, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x00000000004001c4
   04 | ------ IMark(0x4001c4, 6, 0) ------
   05 | STle(t2) = 0x0000000a
   06 | ------ IMark(0x4001ca, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4001cf, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004001d4
   03 | ------ IMark(0x4001d4, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004001d9
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4001d9, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x00000000004001e0
   04 | ------ IMark(0x4001e0, 6, 0) ------
   05 | STle(t2) = 0x0000000b
   06 | ------ IMark(0x4001e6, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4001eb, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004001f0
   03 | ------ IMark(0x4001f0, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004001f5
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4001f5, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x00000000004001fc
   04 | ------ IMark(0x4001fc, 6, 0) ------
   05 | STle(t2) = 0x0000000c
   06 | ------ IMark(0x400202, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400207, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x000000000040020e
   03 | ------ IMark(0x40020e, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400210, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000002f
   16 | PUT(rip) = 0x0000000000400213
   17 | ------ IMark(0x400213, 6, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000002f)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x400299; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400219; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400219, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x0000000000400220
   03 | ------ IMark(0x400220, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400222, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000039
   16 | PUT(rip) = 0x0000000000400225
   17 | ------ IMark(0x400225, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000039)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x400227; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400299; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x400227, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500038)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x000000000040022e
   04 | ------ IMark(0x40022e, 6, 0) ------
   05 | STle(t2) = 0x00000000
   06 | ------ IMark(0x400234, 2, 0) ------
   NEXT: PUT(rip) = 0x000000000040026b; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I8 t8:Ity_I1 t9:Ity_I32 t10:Ity_I32 t11:Ity_I32 t12:Ity_I32 t13:Ity_I32 t14:Ity_I32 t15:Ity_I64 t16:Ity_I64 t17:Ity_I32 t18:Ity_I32 t19:Ity_I32 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I32 t30:Ity_I64 t31:Ity_I32 t32:Ity_I64 t33:Ity_I64 t34:Ity_I64 t35:Ity_I8 t36:Ity_I8 t37:Ity_I64 t38:Ity_I64 t39:Ity_I64 t40:Ity_I64 t41:Ity_I64 t42:Ity_I64 t43:Ity_I32 t44:Ity_I64 t45:Ity_I32 t46:Ity_I64 t47:Ity_I32 t48:Ity_I64 t49:Ity_I64 t50:Ity_I64 t51:Ity_I64 t52:Ity_I32 t53:Ity_I64 t54:Ity_I32 t55:Ity_I64 t56:Ity_I64 t57:Ity_I64 t58:Ity_I64 t59:Ity_I64 t60:Ity_I32 t61:Ity_I64 t62:Ity_I64 t63:Ity_I64 t64:Ity_I32 t65:Ity_I32 t66:Ity_I64 t67:Ity_I32 t68:Ity_I64 t69:Ity_I64 t70:Ity_I64 t71:Ity_I64 t72:Ity_I64 t73:Ity_I64 t74:Ity_I64 t75:Ity_I32 t76:Ity_I64 t77:Ity_I32 t78:Ity_I64 t79:Ity_I64 t80:Ity_I64 t81:Ity_I64 t82:Ity_I64 t83:Ity_I64

   00 | ------ IMark(0x400236, 7, 0) ------
   01 | t25 = LDle:I64(0x0000000000500038)
   02 | PUT(rip) = 0x000000000040023d
   03 | ------ IMark(0x40023d, 2, 0) ------
   04 | t27 = LDle:I32(t25)
   05 | t26 = 32Uto64(t27)
   06 | ------ IMark(0x40023f, 2, 0) ------
   07 | t29 = 64to32(t26)
   08 | t28 = 32Uto64(t29)
   09 | ------ IMark(0x400241, 3, 0) ------
   10 | t31 = 64to32(t28)
   11 | t33 = 32Uto64(t31)
   12 | t5 = Shl64(t33,0x02)
   13 | t43 = 64to32(t5)
   14 | t44 = 32Uto64(t43)
   15 | ------ IMark(0x400244, 2, 0) ------
   16 | t45 = 64to32(t44)
   17 | t47 = 64to32(t26)
   18 | t9 = Add32(t45,t47)
   19 | t51 = 32Uto64(t9)
   20 | ------ IMark(0x400246, 2, 0) ------
   21 | t52 = 64to32(t51)
   22 | t12 = Shl32(t52,0x01)
   23 | t58 = 32Uto64(t12)
   24 | ------ IMark(0x400248, 2, 0) ------
   25 | t60 = 64to32(t58)
   26 | t59 = 32Uto64(t60)
   27 | PUT(rip) = 0x000000000040024a
   28 | ------ IMark(0x40024a, 7, 0) ------
   29 | t62 = LDle:I64(0x0000000000500028)
   30 | PUT(rip) = 0x0000000000400251
   31 | ------ IMark(0x400251, 2, 0) ------
   32 | t64 = LDle:I32(t62)
   33 | t63 = 32Uto64(t64)
   34 | ------ IMark(0x400253, 2, 0) ------
   35 | t65 = 64to32(t63)
   36 | t67 = 64to32(t59)
   37 | t17 = Add32(t65,t67)
   38 | PUT(cc_op) = 0x0000000000000003
   39 | t69 = 32Uto64(t65)
   40 | PUT(cc_dep1) = t69
   41 | t70 = 32Uto64(t67)
   42 | PUT(cc_dep2) = t70
   43 | t71 = 32Uto64(t17)
   44 | ------ IMark(0x400255, 3, 0) ------
   45 | t72 = Add64(t71,0xffffffffffffffd0)
   46 | t75 = 64to32(t72)
   47 | t74 = 32Uto64(t75)
   48 | PUT(rdx) = t74
   49 | PUT(rip) = 0x0000000000400258
   50 | ------ IMark(0x400258, 7, 0) ------
   51 | t76 = LDle:I64(0x0000000000500038)
   52 | PUT(rip) = 0x000000000040025f
   53 | ------ IMark(0x40025f, 2, 0) ------
   54 | t77 = 64to32(t74)
   55 | STle(t76) = t77
   56 | ------ IMark(0x400261, 5, 0) ------
   57 | PUT(rax) = 0x0000000000000000
   58 | PUT(rip) = 0x0000000000400266
   59 | ------ IMark(0x400266, 5, 0) ------
   60 | t81 = GET:I64(rsp)
   61 | t80 = Sub64(t81,0x0000000000000008)
   62 | PUT(rsp) = t80
   63 | STle(t80) = 0x000000000040026b
   64 | t82 = Sub64(t80,0x0000000000000080)
   65 | ====== AbiHint(0xt82, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x40026b, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x0000000000400272
   03 | ------ IMark(0x400272, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400274, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000002f
   16 | PUT(rip) = 0x0000000000400277
   17 | ------ IMark(0x400277, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000002f)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x400287; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400279; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400279, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x0000000000400280
   03 | ------ IMark(0x400280, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400282, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000039
   16 | PUT(rip) = 0x0000000000400285
   17 | ------ IMark(0x400285, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000039)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x400236; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400287; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x400287, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x000000000040028e
   04 | ------ IMark(0x40028e, 6, 0) ------
   05 | STle(t2) = 0x0000000d
   06 | ------ IMark(0x400294, 5, 0) ------
   NEXT: PUT(rip) = 0x00000000004003e8; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400299, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x00000000004002a0
   03 | ------ IMark(0x4002a0, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x4002a2, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000060
   16 | PUT(rip) = 0x00000000004002a5
   17 | ------ IMark(0x4002a5, 6, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000060)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x4003db; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004002ab; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x4002ab, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x00000000004002b2
   03 | ------ IMark(0x4002b2, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x4002b4, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000007a
   16 | PUT(rip) = 0x00000000004002b7
   17 | ------ IMark(0x4002b7, 6, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000007a)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x4002bd; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004003db; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4002bd, 7, 0) ------
   01 | t2 = GET:I64(rbp)
   02 | t1 = Add64(t2,0xfffffffffffffffc)
   03 | STle(t1) = 0x00000000
   04 | ------ IMark(0x4002c4, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004002ee; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I32 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I32 t20:Ity_I64 t21:Ity_I64 t22:Ity_I32 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I32 t27:Ity_I64 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64 t32:Ity_I8 t33:Ity_I64 t34:Ity_I64 t35:Ity_I64 t36:Ity_I64 t37:Ity_I64

   00 | ------ IMark(0x4002c6, 7, 0) ------
   01 | t9 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x00000000004002cd
   03 | ------ IMark(0x4002cd, 2, 0) ------
   04 | t11 = LDle:I32(t9)
   05 | t10 = 32Uto64(t11)
   06 | PUT(rcx) = t10
   07 | PUT(rip) = 0x00000000004002cf
   08 | ------ IMark(0x4002cf, 3, 0) ------
   09 | t13 = GET:I64(rbp)
   10 | t12 = Add64(t13,0xfffffffffffffffc)
   11 | t15 = LDle:I32(t12)
   12 | t14 = 32Uto64(t15)
   13 | ------ IMark(0x4002d2, 3, 0) ------
   14 | t16 = Add64(t14,0x0000000000000001)
   15 | t19 = 64to32(t16)
   16 | t18 = 32Uto64(t19)
   17 | PUT(rip) = 0x00000000004002d5
   18 | ------ IMark(0x4002d5, 3, 0) ------
   19 | t20 = Add64(t13,0xfffffffffffffffc)
   20 | t22 = 64to32(t18)
   21 | STle(t20) = t22
   22 | PUT(rip) = 0x00000000004002d8
   23 | ------ IMark(0x4002d8, 7, 0) ------
   24 | t24 = LDle:I64(0x0000000000500040)
   25 | PUT(rdx) = t24
   26 | ------ IMark(0x4002df, 2, 0) ------
   27 | t26 = 64to32(t14)
   28 | t25 = 32Sto64(t26)
   29 | PUT(rip) = 0x00000000004002e1
   30 | ------ IMark(0x4002e1, 3, 0) ------
   31 | t28 = Add64(t24,t25)
   32 | t32 = GET:I8(cl)
   33 | STle(t28) = t32
   34 | ------ IMark(0x4002e4, 5, 0) ------
   35 | PUT(rax) = 0x0000000000000000
   36 | PUT(rip) = 0x00000000004002e9
   37 | ------ IMark(0x4002e9, 5, 0) ------
   38 | t35 = GET:I64(rsp)
   39 | t34 = Sub64(t35,0x0000000000000008)
   40 | PUT(rsp) = t34
   41 | STle(t34) = 0x00000000004002ee
   42 | t36 = Sub64(t34,0x0000000000000080)
   43 | ====== AbiHint(0xt36, 128, 0x0000000000400034) ======
   NEXT: PUT(rip) = 0x0000000000400034; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x4002ee, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x00000000004002f5
   03 | ------ IMark(0x4002f5, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x4002f7, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000060
   16 | PUT(rip) = 0x00000000004002fa
   17 | ------ IMark(0x4002fa, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000060)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x40030a; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004002fc; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x4002fc, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x0000000000400303
   03 | ------ IMark(0x400303, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400305, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000007a
   16 | PUT(rip) = 0x0000000000400308
   17 | ------ IMark(0x400308, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000007a)
   20 | t23 = CmpLE32S(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x4002c6; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040030a; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x40030a, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500028)
   02 | PUT(rip) = 0x0000000000400311
   03 | ------ IMark(0x400311, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400313, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000005f
   16 | PUT(rip) = 0x0000000000400316
   17 | ------ IMark(0x400316, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000005f)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x4002c6; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400318; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I32 t10:Ity_I64 t11:Ity_I32 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64

   00 | ------ IMark(0x400318, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500040)
   02 | PUT(rdx) = t5
   03 | PUT(rip) = 0x000000000040031f
   04 | ------ IMark(0x40031f, 3, 0) ------
   05 | t7 = GET:I64(rbp)
   06 | t6 = Add64(t7,0xfffffffffffffffc)
   07 | t9 = LDle:I32(t6)
   08 | t8 = 32Uto64(t9)
   09 | ------ IMark(0x400322, 2, 0) ------
   10 | t11 = 64to32(t8)
   11 | t10 = 32Sto64(t11)
   12 | PUT(rip) = 0x0000000000400324
   13 | ------ IMark(0x400324, 4, 0) ------
   14 | t13 = Add64(t5,t10)
   15 | STle(t13) = 0x00
   16 | PUT(rip) = 0x0000000000400328
   17 | ------ IMark(0x400328, 7, 0) ------
   18 | t17 = LDle:I64(0x0000000000500030)
   19 | PUT(rax) = t17
   20 | PUT(rip) = 0x000000000040032f
   21 | ------ IMark(0x40032f, 6, 0) ------
   22 | STle(t17) = 0x00000000
   23 | ------ IMark(0x400335, 2, 0) ------
   NEXT: PUT(rip) = 0x000000000040034c; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I32 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I32 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64 t32:Ity_I64 t33:Ity_I64 t34:Ity_I1 t35:Ity_I64 t36:Ity_I64 t37:Ity_I64 t38:Ity_I64 t39:Ity_I64 t40:Ity_I64 t41:Ity_I64 t42:Ity_I32 t43:Ity_I64 t44:Ity_I32 t45:Ity_I64 t46:Ity_I32 t47:Ity_I64 t48:Ity_I64 t49:Ity_I1 t50:Ity_I1

   00 | ------ IMark(0x400337, 7, 0) ------
   01 | t12 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x000000000040033e
   03 | ------ IMark(0x40033e, 2, 0) ------
   04 | t14 = LDle:I32(t12)
   05 | t41 = 32Uto64(t14)
   06 | t13 = t41
   07 | ------ IMark(0x400340, 3, 0) ------
   08 | t15 = Add64(t13,0x0000000000000001)
   09 | t42 = 64to32(t15)
   10 | t18 = t42
   11 | t43 = 32Uto64(t18)
   12 | t17 = t43
   13 | PUT(rip) = 0x0000000000400343
   14 | ------ IMark(0x400343, 7, 0) ------
   15 | t19 = LDle:I64(0x0000000000500030)
   16 | PUT(rip) = 0x000000000040034a
   17 | ------ IMark(0x40034a, 2, 0) ------
   18 | t44 = 64to32(t17)
   19 | t20 = t44
   20 | STle(t19) = t20
   21 | PUT(rip) = 0x000000000040034c
   22 | ------ IMark(0x40034c, 7, 0) ------
   23 | t22 = LDle:I64(0x0000000000500030)
   24 | PUT(rip) = 0x0000000000400353
   25 | ------ IMark(0x400353, 2, 0) ------
   26 | t24 = LDle:I32(t22)
   27 | t45 = 32Uto64(t24)
   28 | t23 = t45
   29 | PUT(rip) = 0x0000000000400355
   30 | ------ IMark(0x400355, 7, 0) ------
   31 | t25 = LDle:I64(0x0000000000500048)
   32 | ------ IMark(0x40035c, 3, 0) ------
   33 | t46 = 64to32(t23)
   34 | t27 = t46
   35 | t47 = 32Sto64(t27)
   36 | t26 = t47
   37 | PUT(rdx) = t26
   38 | PUT(rip) = 0x000000000040035f
   39 | ------ IMark(0x40035f, 4, 0) ------
   40 | t31 = Shl64(t26,0x03)
   41 | t29 = Add64(t25,t31)
   42 | t33 = LDle:I64(t29)
   43 | PUT(rax) = t33
   44 | ------ IMark(0x400363, 3, 0) ------
   45 | PUT(cc_op) = 0x0000000000000014
   46 | PUT(cc_dep1) = t33
   47 | PUT(cc_dep2) = 0x0000000000000000
   48 | PUT(rip) = 0x0000000000400366
   49 | ------ IMark(0x400366, 2, 0) ------
   50 | t49 = CmpEQ64(t33,0x0000000000000000)
   51 | t48 = 1Uto64(t49)
   52 | t39 = t48
   53 | t50 = 64to1(t39)
   54 | t34 = t50
   55 | if (t34) { PUT(rip) = 0x400395; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400368; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I32 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64

   00 | ------ IMark(0x400368, 7, 0) ------
   01 | t7 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x000000000040036f
   03 | ------ IMark(0x40036f, 2, 0) ------
   04 | t9 = LDle:I32(t7)
   05 | t8 = 32Uto64(t9)
   06 | PUT(rip) = 0x0000000000400371
   07 | ------ IMark(0x400371, 7, 0) ------
   08 | t10 = LDle:I64(0x0000000000500048)
   09 | ------ IMark(0x400378, 3, 0) ------
   10 | t12 = 64to32(t8)
   11 | t11 = 32Sto64(t12)
   12 | PUT(rip) = 0x000000000040037b
   13 | ------ IMark(0x40037b, 4, 0) ------
   14 | t16 = Shl64(t11,0x03)
   15 | t14 = Add64(t10,t16)
   16 | t18 = LDle:I64(t14)
   17 | PUT(rax) = t18
   18 | PUT(rip) = 0x000000000040037f
   19 | ------ IMark(0x40037f, 7, 0) ------
   20 | t19 = LDle:I64(0x0000000000500040)
   21 | PUT(rdx) = t19
   22 | ------ IMark(0x400386, 3, 0) ------
   23 | PUT(rsi) = t19
   24 | ------ IMark(0x400389, 3, 0) ------
   25 | PUT(rdi) = t18
   26 | PUT(rip) = 0x000000000040038c
   27 | ------ IMark(0x40038c, 5, 0) ------
   28 | t23 = GET:I64(rsp)
   29 | t22 = Sub64(t23,0x0000000000000008)
   30 | PUT(rsp) = t22
   31 | STle(t22) = 0x0000000000400391
   32 | t24 = Sub64(t22,0x0000000000000080)
   33 | ====== AbiHint(0xt24, 128, 0x0000000000500050) ======
   NEXT: PUT(rip) = 0x0000000000500050; Ijk_Call
}",
  "IRSB {
   t0:Ity_I32 t1:Ity_I32 t2:Ity_I32 t3:Ity_I32 t4:Ity_I64 t5:Ity_I32 t6:Ity_I64 t7:Ity_I64 t8:Ity_I1 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I64 t17:Ity_I64 t18:Ity_I1 t19:Ity_I32 t20:Ity_I1

   00 | ------ IMark(0x400391, 2, 0) ------
   01 | t4 = GET:I64(rax)
   02 | t15 = 64to32(t4)
   03 | t3 = t15
   04 | PUT(cc_op) = 0x0000000000000013
   05 | t16 = 32Uto64(t3)
   06 | t7 = t16
   07 | PUT(cc_dep1) = t7
   08 | PUT(cc_dep2) = 0x0000000000000000
   09 | PUT(rip) = 0x0000000000400393
   10 | ------ IMark(0x400393, 2, 0) ------
   11 | t19 = 64to32(t7)
   12 | t18 = CmpEQ32(t19,0x00000000)
   13 | t17 = 1Uto64(t18)
   14 | t13 = t17
   15 | t20 = 64to1(t13)
   16 | t8 = t20
   17 | if (t8) { PUT(rip) = 0x400395; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400337; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I32 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I1 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I64 t30:Ity_I1 t31:Ity_I1

   00 | ------ IMark(0x400395, 7, 0) ------
   01 | t7 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x000000000040039c
   03 | ------ IMark(0x40039c, 2, 0) ------
   04 | t9 = LDle:I32(t7)
   05 | t26 = 32Uto64(t9)
   06 | t8 = t26
   07 | PUT(rip) = 0x000000000040039e
   08 | ------ IMark(0x40039e, 7, 0) ------
   09 | t10 = LDle:I64(0x0000000000500048)
   10 | ------ IMark(0x4003a5, 3, 0) ------
   11 | t27 = 64to32(t8)
   12 | t12 = t27
   13 | t28 = 32Sto64(t12)
   14 | t11 = t28
   15 | PUT(rdx) = t11
   16 | PUT(rip) = 0x00000000004003a8
   17 | ------ IMark(0x4003a8, 4, 0) ------
   18 | t16 = Shl64(t11,0x03)
   19 | t14 = Add64(t10,t16)
   20 | t18 = LDle:I64(t14)
   21 | PUT(rax) = t18
   22 | ------ IMark(0x4003ac, 3, 0) ------
   23 | PUT(cc_op) = 0x0000000000000014
   24 | PUT(cc_dep1) = t18
   25 | PUT(cc_dep2) = 0x0000000000000000
   26 | PUT(rip) = 0x00000000004003af
   27 | ------ IMark(0x4003af, 2, 0) ------
   28 | t30 = CmpEQ64(t18,0x0000000000000000)
   29 | t29 = 1Uto64(t30)
   30 | t24 = t29
   31 | t31 = 64to1(t24)
   32 | t19 = t31
   33 | if (t19) { PUT(rip) = 0x4003b1; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004003e7; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I8 t3:Ity_I8 t4:Ity_I8 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I32 t10:Ity_I8 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I32 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I64 t25:Ity_I1

   00 | ------ IMark(0x4003b1, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500040)
   02 | PUT(rip) = 0x00000000004003b8
   03 | ------ IMark(0x4003b8, 4, 0) ------
   04 | t6 = Add64(t5,0x0000000000000001)
   05 | t10 = LDle:I8(t6)
   06 | t19 = 8Uto32(t10)
   07 | t9 = t19
   08 | t20 = 32Uto64(t9)
   09 | t8 = t20
   10 | PUT(rax) = t8
   11 | ------ IMark(0x4003bc, 2, 0) ------
   12 | t4 = GET:I8(al)
   13 | PUT(cc_op) = 0x0000000000000011
   14 | t21 = 8Uto64(t4)
   15 | t11 = t21
   16 | PUT(cc_dep1) = t11
   17 | PUT(cc_dep2) = 0x0000000000000000
   18 | PUT(rip) = 0x00000000004003be
   19 | ------ IMark(0x4003be, 2, 0) ------
   20 | t24 = And64(t11,0x00000000000000ff)
   21 | t23 = CmpEQ64(t24,0x0000000000000000)
   22 | t22 = 1Uto64(t23)
   23 | t17 = t22
   24 | t25 = 64to1(t17)
   25 | t12 = t25
   26 | if (t12) { PUT(rip) = 0x4003c0; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004003cf; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64

   00 | ------ IMark(0x4003c0, 7, 0) ------
   01 | t2 = LDle:I64(0x0000000000500030)
   02 | PUT(rax) = t2
   03 | PUT(rip) = 0x00000000004003c7
   04 | ------ IMark(0x4003c7, 6, 0) ------
   05 | STle(t2) = 0x0000000e
   06 | ------ IMark(0x4003cd, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004003e7; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4003cf, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004003d4
   03 | ------ IMark(0x4003d4, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004003d9
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4003d9, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004003e7; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4003db, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004003e0
   03 | ------ IMark(0x4003e0, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004003e5
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4003e5, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4003e7, 1, 0) ------
   01 | ------ IMark(0x4003e8, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004003ef; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4003ea, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400077; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I32 t11:Ity_I32 t12:Ity_I32 t13:Ity_I32 t14:Ity_I32 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I32 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I64 t29:Ity_I32 t30:Ity_I64 t31:Ity_I32 t32:Ity_I64 t33:Ity_I64 t34:Ity_I64 t35:Ity_I64 t36:Ity_I32 t37:Ity_I64 t38:Ity_I32 t39:Ity_I64 t40:Ity_I64 t41:Ity_I64 t42:Ity_I64 t43:Ity_I32 t44:Ity_I64 t45:Ity_I32 t46:Ity_I64 t47:Ity_I64 t48:Ity_I64 t49:Ity_I64 t50:Ity_I32 t51:Ity_I64 t52:Ity_I32 t53:Ity_I64 t54:Ity_I64 t55:Ity_I64 t56:Ity_I64 t57:Ity_I64

   00 | ------ IMark(0x4003ef, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | PUT(rsp) = t0
   03 | t1 = LDle:I64(t0)
   04 | PUT(rbp) = t1
   05 | t20 = Add64(t0,0x0000000000000008)
   06 | PUT(rsp) = t20
   07 | ------ IMark(0x4003f0, 2, 0) ------
   08 | PUT(rax) = 0x0000000000000000
   09 | ------ IMark(0x4003f2, 2, 0) ------
   10 | PUT(rdx) = 0x0000000000000000
   11 | ------ IMark(0x4003f4, 2, 0) ------
   12 | PUT(rcx) = 0x0000000000000000
   13 | ------ IMark(0x4003f6, 2, 0) ------
   14 | PUT(rsi) = 0x0000000000000000
   15 | ------ IMark(0x4003f8, 2, 0) ------
   16 | PUT(cc_op) = 0x0000000000000013
   17 | PUT(cc_dep1) = 0x0000000000000000
   18 | PUT(cc_dep2) = 0x0000000000000000
   19 | PUT(rdi) = 0x0000000000000000
   20 | PUT(rip) = 0x00000000004003fa
   21 | ------ IMark(0x4003fa, 1, 0) ------
   22 | t18 = LDle:I64(t20)
   23 | t19 = Add64(t20,0x0000000000000008)
   24 | PUT(rsp) = t19
   25 | t56 = Sub64(t19,0x0000000000000080)
   26 | ====== AbiHint(0xt56, 128, t18) ======
   NEXT: PUT(rip) = t18; Ijk_Ret
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I32 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64

   00 | ------ IMark(0x4003fb, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t9 = GET:I64(rsp)
   03 | t8 = Sub64(t9,0x0000000000000008)
   04 | PUT(rsp) = t8
   05 | STle(t8) = t0
   06 | ------ IMark(0x4003fc, 3, 0) ------
   07 | PUT(rbp) = t8
   08 | ------ IMark(0x4003ff, 4, 0) ------
   09 | t2 = Sub64(t8,0x0000000000000020)
   10 | PUT(cc_op) = 0x0000000000000008
   11 | PUT(cc_dep1) = t8
   12 | PUT(cc_dep2) = 0x0000000000000020
   13 | PUT(rsp) = t2
   14 | PUT(rip) = 0x0000000000400403
   15 | ------ IMark(0x400403, 3, 0) ------
   16 | t11 = Add64(t8,0xffffffffffffffec)
   17 | t14 = GET:I64(rdi)
   18 | t13 = 64to32(t14)
   19 | STle(t11) = t13
   20 | ------ IMark(0x400406, 5, 0) ------
   21 | PUT(rdi) = 0x0000000000000028
   22 | PUT(rip) = 0x000000000040040b
   23 | ------ IMark(0x40040b, 5, 0) ------
   24 | t16 = Sub64(t2,0x0000000000000008)
   25 | PUT(rsp) = t16
   26 | STle(t16) = 0x0000000000400410
   27 | t18 = Sub64(t16,0x0000000000000080)
   28 | ====== AbiHint(0xt18, 128, 0x0000000000500058) ======
   NEXT: PUT(rip) = 0x0000000000500058; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I32 t11:Ity_I32 t12:Ity_I32 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I32 t26:Ity_I32 t27:Ity_I64 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64 t32:Ity_I64 t33:Ity_I32 t34:Ity_I64 t35:Ity_I32 t36:Ity_I64 t37:Ity_I64 t38:Ity_I64 t39:Ity_I64 t40:Ity_I32 t41:Ity_I64 t42:Ity_I32 t43:Ity_I64 t44:Ity_I64 t45:Ity_I64 t46:Ity_I64 t47:Ity_I64

   00 | ------ IMark(0x400410, 4, 0) ------
   01 | t17 = GET:I64(rbp)
   02 | t16 = Add64(t17,0xfffffffffffffff8)
   03 | t18 = GET:I64(rax)
   04 | STle(t16) = t18
   05 | PUT(rip) = 0x0000000000400414
   06 | ------ IMark(0x400414, 4, 0) ------
   07 | t19 = Add64(t17,0xfffffffffffffff8)
   08 | t21 = LDle:I64(t19)
   09 | PUT(rip) = 0x0000000000400418
   10 | ------ IMark(0x400418, 3, 0) ------
   11 | t22 = Add64(t17,0xffffffffffffffec)
   12 | t25 = LDle:I32(t22)
   13 | t24 = 32Uto64(t25)
   14 | PUT(rip) = 0x000000000040041b
   15 | ------ IMark(0x40041b, 2, 0) ------
   16 | t26 = 64to32(t24)
   17 | STle(t21) = t26
   18 | PUT(rip) = 0x000000000040041d
   19 | ------ IMark(0x40041d, 4, 0) ------
   20 | t28 = Add64(t17,0xfffffffffffffff8)
   21 | t30 = LDle:I64(t28)
   22 | PUT(rax) = t30
   23 | PUT(rip) = 0x0000000000400421
   24 | ------ IMark(0x400421, 1, 0) ------
   25 | PUT(rsp) = t17
   26 | t6 = LDle:I64(t17)
   27 | PUT(rbp) = t6
   28 | t31 = Add64(t17,0x0000000000000008)
   29 | PUT(rsp) = t31
   30 | ------ IMark(0x400422, 2, 0) ------
   31 | PUT(rdx) = 0x0000000000000000
   32 | ------ IMark(0x400424, 2, 0) ------
   33 | PUT(cc_op) = 0x0000000000000013
   34 | PUT(cc_dep1) = 0x0000000000000000
   35 | PUT(cc_dep2) = 0x0000000000000000
   36 | PUT(rdi) = 0x0000000000000000
   37 | PUT(rip) = 0x0000000000400426
   38 | ------ IMark(0x400426, 1, 0) ------
   39 | t14 = LDle:I64(t31)
   40 | t15 = Add64(t31,0x0000000000000008)
   41 | PUT(rsp) = t15
   42 | t46 = Sub64(t15,0x0000000000000080)
   43 | ====== AbiHint(0xt46, 128, t14) ======
   NEXT: PUT(rip) = t14; Ijk_Ret
}"
]

#guard
  (nextSymBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  match parseProgram nextSymBlocks with
  | .ok _ => true
  | .error _ => false
