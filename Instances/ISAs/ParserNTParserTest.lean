import Instances.ISAs.VexIRParser

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## Roundtrip test: all parser NT blocks parse without error -/
-- Embedded from reference/tinyc/parser_nt_blocks.json

def termBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x400427, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t11 = GET:I64(rsp)
   03 | t10 = Sub64(t11,0x0000000000000008)
   04 | PUT(rsp) = t10
   05 | STle(t10) = t0
   06 | ------ IMark(0x400428, 3, 0) ------
   07 | PUT(rbp) = t10
   08 | ------ IMark(0x40042b, 4, 0) ------
   09 | t2 = Sub64(t10,0x0000000000000010)
   10 | PUT(rsp) = t2
   11 | PUT(rip) = 0x000000000040042f
   12 | ------ IMark(0x40042f, 7, 0) ------
   13 | t13 = LDle:I64(0x0000000000500030)
   14 | PUT(rip) = 0x0000000000400436
   15 | ------ IMark(0x400436, 2, 0) ------
   16 | t15 = LDle:I32(t13)
   17 | t27 = 32Uto64(t15)
   18 | t14 = t27
   19 | PUT(rax) = t14
   20 | ------ IMark(0x400438, 3, 0) ------
   21 | t28 = 64to32(t14)
   22 | t16 = t28
   23 | PUT(cc_op) = 0x0000000000000007
   24 | t29 = 32Uto64(t16)
   25 | t18 = t29
   26 | PUT(cc_dep1) = t18
   27 | PUT(cc_dep2) = 0x000000000000000e
   28 | PUT(rip) = 0x000000000040043b
   29 | ------ IMark(0x40043b, 2, 0) ------
   30 | t32 = 64to32(t18)
   31 | t33 = 64to32(0x000000000000000e)
   32 | t31 = CmpEQ32(t32,t33)
   33 | t30 = 1Uto64(t31)
   34 | t25 = t30
   35 | t34 = 64to1(t25)
   36 | t20 = t34
   37 | if (t20) { PUT(rip) = 0x40043d; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040046e; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40043d, 5, 0) ------
   01 | PUT(rdi) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400442
   03 | ------ IMark(0x400442, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400447
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I32 t14:Ity_I8 t15:Ity_I64 t16:Ity_I32 t17:Ity_I8 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I32 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64 t32:Ity_I64 t33:Ity_I64

   00 | ------ IMark(0x400447, 4, 0) ------
   01 | t9 = GET:I64(rbp)
   02 | t8 = Add64(t9,0xfffffffffffffff8)
   03 | t10 = GET:I64(rax)
   04 | STle(t8) = t10
   05 | PUT(rip) = 0x000000000040044b
   06 | ------ IMark(0x40044b, 7, 0) ------
   07 | t11 = LDle:I64(0x0000000000500040)
   08 | PUT(rip) = 0x0000000000400452
   09 | ------ IMark(0x400452, 3, 0) ------
   10 | t14 = LDle:I8(t11)
   11 | t13 = 8Uto32(t14)
   12 | t12 = 32Uto64(t13)
   13 | PUT(rax) = t12
   14 | ------ IMark(0x400455, 3, 0) ------
   15 | t17 = GET:I8(al)
   16 | t16 = 8Sto32(t17)
   17 | t15 = 32Uto64(t16)
   18 | ------ IMark(0x400458, 3, 0) ------
   19 | t18 = Add64(t15,0xffffffffffffff9f)
   20 | t21 = 64to32(t18)
   21 | t20 = 32Uto64(t21)
   22 | PUT(rdx) = t20
   23 | PUT(rip) = 0x000000000040045b
   24 | ------ IMark(0x40045b, 4, 0) ------
   25 | t22 = Add64(t9,0xfffffffffffffff8)
   26 | t24 = LDle:I64(t22)
   27 | PUT(rip) = 0x000000000040045f
   28 | ------ IMark(0x40045f, 3, 0) ------
   29 | t25 = Add64(t24,0x0000000000000020)
   30 | t27 = 64to32(t20)
   31 | STle(t25) = t27
   32 | ------ IMark(0x400462, 5, 0) ------
   33 | PUT(rax) = 0x0000000000000000
   34 | PUT(rip) = 0x0000000000400467
   35 | ------ IMark(0x400467, 5, 0) ------
   36 | t31 = GET:I64(rsp)
   37 | t30 = Sub64(t31,0x0000000000000008)
   38 | PUT(rsp) = t30
   39 | STle(t30) = 0x000000000040046c
   40 | t32 = Sub64(t30,0x0000000000000080)
   41 | ====== AbiHint(0xt32, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x40046c, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004004b4; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x40046e, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x0000000000400475
   03 | ------ IMark(0x400475, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400477, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000000d
   16 | PUT(rip) = 0x000000000040047a
   17 | ------ IMark(0x40047a, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000000d)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x40047c; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004004a6; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40047c, 5, 0) ------
   01 | PUT(rdi) = 0x0000000000000001
   02 | PUT(rip) = 0x0000000000400481
   03 | ------ IMark(0x400481, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400486
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I32 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I32 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64

   00 | ------ IMark(0x400486, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff8)
   03 | t9 = GET:I64(rax)
   04 | STle(t7) = t9
   05 | PUT(rip) = 0x000000000040048a
   06 | ------ IMark(0x40048a, 7, 0) ------
   07 | t10 = LDle:I64(0x0000000000500038)
   08 | PUT(rip) = 0x0000000000400491
   09 | ------ IMark(0x400491, 2, 0) ------
   10 | t12 = LDle:I32(t10)
   11 | t11 = 32Uto64(t12)
   12 | PUT(rdx) = t11
   13 | PUT(rip) = 0x0000000000400493
   14 | ------ IMark(0x400493, 4, 0) ------
   15 | t13 = Add64(t8,0xfffffffffffffff8)
   16 | t15 = LDle:I64(t13)
   17 | PUT(rip) = 0x0000000000400497
   18 | ------ IMark(0x400497, 3, 0) ------
   19 | t16 = Add64(t15,0x0000000000000020)
   20 | t18 = 64to32(t11)
   21 | STle(t16) = t18
   22 | ------ IMark(0x40049a, 5, 0) ------
   23 | PUT(rax) = 0x0000000000000000
   24 | PUT(rip) = 0x000000000040049f
   25 | ------ IMark(0x40049f, 5, 0) ------
   26 | t22 = GET:I64(rsp)
   27 | t21 = Sub64(t22,0x0000000000000008)
   28 | PUT(rsp) = t21
   29 | STle(t21) = 0x00000000004004a4
   30 | t23 = Sub64(t21,0x0000000000000080)
   31 | ====== AbiHint(0xt23, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4004a4, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004004b4; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4004a6, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004004ab
   03 | ------ IMark(0x4004ab, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004004b0
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040064d) ======
   NEXT: PUT(rip) = 0x000000000040064d; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I32 t22:Ity_I64 t23:Ity_I32 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I32 t31:Ity_I64 t32:Ity_I64 t33:Ity_I64 t34:Ity_I64 t35:Ity_I64

   00 | ------ IMark(0x4004b0, 4, 0) ------
   01 | t14 = GET:I64(rbp)
   02 | t13 = Add64(t14,0xfffffffffffffff8)
   03 | t15 = GET:I64(rax)
   04 | STle(t13) = t15
   05 | PUT(rip) = 0x00000000004004b4
   06 | ------ IMark(0x4004b4, 4, 0) ------
   07 | t16 = Add64(t14,0xfffffffffffffff8)
   08 | t18 = LDle:I64(t16)
   09 | PUT(rax) = t18
   10 | PUT(rip) = 0x00000000004004b8
   11 | ------ IMark(0x4004b8, 1, 0) ------
   12 | PUT(rsp) = t14
   13 | t3 = LDle:I64(t14)
   14 | PUT(rbp) = t3
   15 | t19 = Add64(t14,0x0000000000000008)
   16 | PUT(rsp) = t19
   17 | ------ IMark(0x4004b9, 2, 0) ------
   18 | PUT(rdx) = 0x0000000000000000
   19 | ------ IMark(0x4004bb, 2, 0) ------
   20 | PUT(cc_op) = 0x0000000000000013
   21 | PUT(cc_dep1) = 0x0000000000000000
   22 | PUT(cc_dep2) = 0x0000000000000000
   23 | PUT(rdi) = 0x0000000000000000
   24 | PUT(rip) = 0x00000000004004bd
   25 | ------ IMark(0x4004bd, 1, 0) ------
   26 | t11 = LDle:I64(t19)
   27 | t12 = Add64(t19,0x0000000000000008)
   28 | PUT(rsp) = t12
   29 | t34 = Sub64(t12,0x0000000000000080)
   30 | ====== AbiHint(0xt34, 128, t11) ======
   NEXT: PUT(rip) = t11; Ijk_Ret
}"
]

def sumBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x4004be, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t8 = GET:I64(rsp)
   03 | t7 = Sub64(t8,0x0000000000000008)
   04 | PUT(rsp) = t7
   05 | STle(t7) = t0
   06 | ------ IMark(0x4004bf, 3, 0) ------
   07 | PUT(rbp) = t7
   08 | ------ IMark(0x4004c2, 4, 0) ------
   09 | t2 = Sub64(t7,0x0000000000000010)
   10 | PUT(cc_op) = 0x0000000000000008
   11 | PUT(cc_dep1) = t7
   12 | PUT(cc_dep2) = 0x0000000000000010
   13 | ------ IMark(0x4004c6, 5, 0) ------
   14 | PUT(rax) = 0x0000000000000000
   15 | PUT(rip) = 0x00000000004004cb
   16 | ------ IMark(0x4004cb, 5, 0) ------
   17 | t11 = Sub64(t2,0x0000000000000008)
   18 | PUT(rsp) = t11
   19 | STle(t11) = 0x00000000004004d0
   20 | t13 = Sub64(t11,0x0000000000000080)
   21 | ====== AbiHint(0xt13, 128, 0x0000000000400427) ======
   NEXT: PUT(rip) = 0x0000000000400427; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64

   00 | ------ IMark(0x4004d0, 4, 0) ------
   01 | t2 = GET:I64(rbp)
   02 | t1 = Add64(t2,0xfffffffffffffff0)
   03 | t3 = GET:I64(rax)
   04 | STle(t1) = t3
   05 | ------ IMark(0x4004d4, 2, 0) ------
   NEXT: PUT(rip) = 0x000000000040052b; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4004d6, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rip) = 0x00000000004004da
   05 | ------ IMark(0x4004da, 4, 0) ------
   06 | t10 = Add64(t8,0xfffffffffffffff8)
   07 | STle(t10) = t9
   08 | PUT(rip) = 0x00000000004004de
   09 | ------ IMark(0x4004de, 7, 0) ------
   10 | t13 = LDle:I64(0x0000000000500030)
   11 | PUT(rip) = 0x00000000004004e5
   12 | ------ IMark(0x4004e5, 2, 0) ------
   13 | t15 = LDle:I32(t13)
   14 | t27 = 32Uto64(t15)
   15 | t14 = t27
   16 | PUT(rax) = t14
   17 | ------ IMark(0x4004e7, 3, 0) ------
   18 | t28 = 64to32(t14)
   19 | t16 = t28
   20 | PUT(cc_op) = 0x0000000000000007
   21 | t29 = 32Uto64(t16)
   22 | t18 = t29
   23 | PUT(cc_dep1) = t18
   24 | PUT(cc_dep2) = 0x0000000000000008
   25 | PUT(rip) = 0x00000000004004ea
   26 | ------ IMark(0x4004ea, 2, 0) ------
   27 | t32 = 64to32(t18)
   28 | t33 = 64to32(0x0000000000000008)
   29 | t31 = CmpEQ32(t32,t33)
   30 | t30 = 1Uto64(t31)
   31 | t25 = t30
   32 | t34 = 64to1(t25)
   33 | t20 = t34
   34 | if (t20) { PUT(rip) = 0x4004ec; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004004f3; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64

   00 | ------ IMark(0x4004ec, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000002
   02 | ------ IMark(0x4004f1, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004004f8; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64

   00 | ------ IMark(0x4004f3, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000003
   02 | ------ IMark(0x4004f8, 2, 0) ------
   03 | PUT(rdi) = 0x0000000000000003
   04 | PUT(rip) = 0x00000000004004fa
   05 | ------ IMark(0x4004fa, 5, 0) ------
   06 | t7 = GET:I64(rsp)
   07 | t6 = Sub64(t7,0x0000000000000008)
   08 | PUT(rsp) = t6
   09 | STle(t6) = 0x00000000004004ff
   10 | t8 = Sub64(t6,0x0000000000000080)
   11 | ====== AbiHint(0xt8, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x4004ff, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x400503, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x0000000000400508
   08 | ------ IMark(0x400508, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x000000000040050d
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64

   00 | ------ IMark(0x40050d, 4, 0) ------
   01 | t6 = GET:I64(rbp)
   02 | t5 = Add64(t6,0xfffffffffffffff0)
   03 | t7 = LDle:I64(t5)
   04 | PUT(rip) = 0x0000000000400511
   05 | ------ IMark(0x400511, 4, 0) ------
   06 | t8 = Add64(t6,0xfffffffffffffff8)
   07 | t10 = LDle:I64(t8)
   08 | PUT(rdx) = t10
   09 | PUT(rip) = 0x0000000000400515
   10 | ------ IMark(0x400515, 4, 0) ------
   11 | t11 = Add64(t7,0x0000000000000008)
   12 | STle(t11) = t10
   13 | ------ IMark(0x400519, 5, 0) ------
   14 | PUT(rax) = 0x0000000000000000
   15 | PUT(rip) = 0x000000000040051e
   16 | ------ IMark(0x40051e, 5, 0) ------
   17 | t16 = GET:I64(rsp)
   18 | t15 = Sub64(t16,0x0000000000000008)
   19 | PUT(rsp) = t15
   20 | STle(t15) = 0x0000000000400523
   21 | t17 = Sub64(t15,0x0000000000000080)
   22 | ====== AbiHint(0xt17, 128, 0x0000000000400427) ======
   NEXT: PUT(rip) = 0x0000000000400427; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x400523, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rdx) = t9
   05 | PUT(rip) = 0x0000000000400527
   06 | ------ IMark(0x400527, 4, 0) ------
   07 | t10 = Add64(t9,0x0000000000000010)
   08 | t12 = GET:I64(rax)
   09 | STle(t10) = t12
   10 | PUT(rip) = 0x000000000040052b
   11 | ------ IMark(0x40052b, 7, 0) ------
   12 | t13 = LDle:I64(0x0000000000500030)
   13 | PUT(rip) = 0x0000000000400532
   14 | ------ IMark(0x400532, 2, 0) ------
   15 | t15 = LDle:I32(t13)
   16 | t27 = 32Uto64(t15)
   17 | t14 = t27
   18 | PUT(rax) = t14
   19 | ------ IMark(0x400534, 3, 0) ------
   20 | t28 = 64to32(t14)
   21 | t16 = t28
   22 | PUT(cc_op) = 0x0000000000000007
   23 | t29 = 32Uto64(t16)
   24 | t18 = t29
   25 | PUT(cc_dep1) = t18
   26 | PUT(cc_dep2) = 0x0000000000000008
   27 | PUT(rip) = 0x0000000000400537
   28 | ------ IMark(0x400537, 2, 0) ------
   29 | t32 = 64to32(t18)
   30 | t33 = 64to32(0x0000000000000008)
   31 | t31 = CmpEQ32(t32,t33)
   32 | t30 = 1Uto64(t31)
   33 | t25 = t30
   34 | t34 = 64to1(t25)
   35 | t20 = t34
   36 | if (t20) { PUT(rip) = 0x4004d6; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400539; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400539, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x0000000000400540
   03 | ------ IMark(0x400540, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400542, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000009
   16 | PUT(rip) = 0x0000000000400545
   17 | ------ IMark(0x400545, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000009)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x4004d6; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400547; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I32 t18:Ity_I64 t19:Ity_I32 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I32 t27:Ity_I64 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64

   00 | ------ IMark(0x400547, 4, 0) ------
   01 | t13 = GET:I64(rbp)
   02 | t12 = Add64(t13,0xfffffffffffffff0)
   03 | t14 = LDle:I64(t12)
   04 | PUT(rax) = t14
   05 | PUT(rip) = 0x000000000040054b
   06 | ------ IMark(0x40054b, 1, 0) ------
   07 | PUT(rsp) = t13
   08 | t2 = LDle:I64(t13)
   09 | PUT(rbp) = t2
   10 | t15 = Add64(t13,0x0000000000000008)
   11 | PUT(rsp) = t15
   12 | ------ IMark(0x40054c, 2, 0) ------
   13 | PUT(rdx) = 0x0000000000000000
   14 | ------ IMark(0x40054e, 2, 0) ------
   15 | PUT(cc_op) = 0x0000000000000013
   16 | PUT(cc_dep1) = 0x0000000000000000
   17 | PUT(cc_dep2) = 0x0000000000000000
   18 | PUT(rdi) = 0x0000000000000000
   19 | PUT(rip) = 0x0000000000400550
   20 | ------ IMark(0x400550, 1, 0) ------
   21 | t10 = LDle:I64(t15)
   22 | t11 = Add64(t15,0x0000000000000008)
   23 | PUT(rsp) = t11
   24 | t30 = Sub64(t11,0x0000000000000080)
   25 | ====== AbiHint(0xt30, 128, t10) ======
   NEXT: PUT(rip) = t10; Ijk_Ret
}"
]

def testBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x400551, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t8 = GET:I64(rsp)
   03 | t7 = Sub64(t8,0x0000000000000008)
   04 | PUT(rsp) = t7
   05 | STle(t7) = t0
   06 | ------ IMark(0x400552, 3, 0) ------
   07 | PUT(rbp) = t7
   08 | ------ IMark(0x400555, 4, 0) ------
   09 | t2 = Sub64(t7,0x0000000000000010)
   10 | PUT(cc_op) = 0x0000000000000008
   11 | PUT(cc_dep1) = t7
   12 | PUT(cc_dep2) = 0x0000000000000010
   13 | ------ IMark(0x400559, 5, 0) ------
   14 | PUT(rax) = 0x0000000000000000
   15 | PUT(rip) = 0x000000000040055e
   16 | ------ IMark(0x40055e, 5, 0) ------
   17 | t11 = Sub64(t2,0x0000000000000008)
   18 | PUT(rsp) = t11
   19 | STle(t11) = 0x0000000000400563
   20 | t13 = Sub64(t11,0x0000000000000080)
   21 | ====== AbiHint(0xt13, 128, 0x00000000004004be) ======
   NEXT: PUT(rip) = 0x00000000004004be; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I32 t12:Ity_I32 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I1 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I64 t27:Ity_I1 t28:Ity_I32 t29:Ity_I32 t30:Ity_I1

   00 | ------ IMark(0x400563, 4, 0) ------
   01 | t7 = GET:I64(rbp)
   02 | t6 = Add64(t7,0xfffffffffffffff0)
   03 | t8 = GET:I64(rax)
   04 | STle(t6) = t8
   05 | PUT(rip) = 0x0000000000400567
   06 | ------ IMark(0x400567, 7, 0) ------
   07 | t9 = LDle:I64(0x0000000000500030)
   08 | PUT(rip) = 0x000000000040056e
   09 | ------ IMark(0x40056e, 2, 0) ------
   10 | t11 = LDle:I32(t9)
   11 | t23 = 32Uto64(t11)
   12 | t10 = t23
   13 | PUT(rax) = t10
   14 | ------ IMark(0x400570, 3, 0) ------
   15 | t24 = 64to32(t10)
   16 | t12 = t24
   17 | PUT(cc_op) = 0x0000000000000007
   18 | t25 = 32Uto64(t12)
   19 | t14 = t25
   20 | PUT(cc_dep1) = t14
   21 | PUT(cc_dep2) = 0x000000000000000a
   22 | PUT(rip) = 0x0000000000400573
   23 | ------ IMark(0x400573, 2, 0) ------
   24 | t28 = 64to32(t14)
   25 | t29 = 64to32(0x000000000000000a)
   26 | t27 = CmpEQ32(t28,t29)
   27 | t26 = 1Uto64(t27)
   28 | t21 = t26
   29 | t30 = 64to1(t21)
   30 | t16 = t30
   31 | if (t16) { PUT(rip) = 0x400575; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004005b3; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x400575, 4, 0) ------
   01 | t5 = GET:I64(rbp)
   02 | t4 = Add64(t5,0xfffffffffffffff0)
   03 | t6 = LDle:I64(t4)
   04 | PUT(rax) = t6
   05 | PUT(rip) = 0x0000000000400579
   06 | ------ IMark(0x400579, 4, 0) ------
   07 | t7 = Add64(t5,0xfffffffffffffff8)
   08 | STle(t7) = t6
   09 | ------ IMark(0x40057d, 5, 0) ------
   10 | PUT(rdi) = 0x0000000000000004
   11 | PUT(rip) = 0x0000000000400582
   12 | ------ IMark(0x400582, 5, 0) ------
   13 | t12 = GET:I64(rsp)
   14 | t11 = Sub64(t12,0x0000000000000008)
   15 | PUT(rsp) = t11
   16 | STle(t11) = 0x0000000000400587
   17 | t13 = Sub64(t11,0x0000000000000080)
   18 | ====== AbiHint(0xt13, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x400587, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x40058b, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x0000000000400590
   08 | ------ IMark(0x400590, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x0000000000400595
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64

   00 | ------ IMark(0x400595, 4, 0) ------
   01 | t6 = GET:I64(rbp)
   02 | t5 = Add64(t6,0xfffffffffffffff0)
   03 | t7 = LDle:I64(t5)
   04 | PUT(rip) = 0x0000000000400599
   05 | ------ IMark(0x400599, 4, 0) ------
   06 | t8 = Add64(t6,0xfffffffffffffff8)
   07 | t10 = LDle:I64(t8)
   08 | PUT(rdx) = t10
   09 | PUT(rip) = 0x000000000040059d
   10 | ------ IMark(0x40059d, 4, 0) ------
   11 | t11 = Add64(t7,0x0000000000000008)
   12 | STle(t11) = t10
   13 | ------ IMark(0x4005a1, 5, 0) ------
   14 | PUT(rax) = 0x0000000000000000
   15 | PUT(rip) = 0x00000000004005a6
   16 | ------ IMark(0x4005a6, 5, 0) ------
   17 | t16 = GET:I64(rsp)
   18 | t15 = Sub64(t16,0x0000000000000008)
   19 | PUT(rsp) = t15
   20 | STle(t15) = 0x00000000004005ab
   21 | t17 = Sub64(t15,0x0000000000000080)
   22 | ====== AbiHint(0xt17, 128, 0x00000000004004be) ======
   NEXT: PUT(rip) = 0x00000000004004be; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I32 t6:Ity_I32 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I32 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I32 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64 t32:Ity_I32 t33:Ity_I64 t34:Ity_I32 t35:Ity_I64 t36:Ity_I64 t37:Ity_I64 t38:Ity_I64 t39:Ity_I64

   00 | ------ IMark(0x4005ab, 4, 0) ------
   01 | t15 = GET:I64(rbp)
   02 | t14 = Add64(t15,0xfffffffffffffff0)
   03 | t16 = LDle:I64(t14)
   04 | PUT(rip) = 0x00000000004005af
   05 | ------ IMark(0x4005af, 4, 0) ------
   06 | t17 = Add64(t16,0x0000000000000010)
   07 | t19 = GET:I64(rax)
   08 | STle(t17) = t19
   09 | PUT(rip) = 0x00000000004005b3
   10 | ------ IMark(0x4005b3, 4, 0) ------
   11 | t20 = Add64(t15,0xfffffffffffffff0)
   12 | t22 = LDle:I64(t20)
   13 | PUT(rax) = t22
   14 | PUT(rip) = 0x00000000004005b7
   15 | ------ IMark(0x4005b7, 1, 0) ------
   16 | PUT(rsp) = t15
   17 | t4 = LDle:I64(t15)
   18 | PUT(rbp) = t4
   19 | t23 = Add64(t15,0x0000000000000008)
   20 | PUT(rsp) = t23
   21 | ------ IMark(0x4005b8, 2, 0) ------
   22 | PUT(rdx) = 0x0000000000000000
   23 | ------ IMark(0x4005ba, 2, 0) ------
   24 | PUT(cc_op) = 0x0000000000000013
   25 | PUT(cc_dep1) = 0x0000000000000000
   26 | PUT(cc_dep2) = 0x0000000000000000
   27 | PUT(rdi) = 0x0000000000000000
   28 | PUT(rip) = 0x00000000004005bc
   29 | ------ IMark(0x4005bc, 1, 0) ------
   30 | t12 = LDle:I64(t23)
   31 | t13 = Add64(t23,0x0000000000000008)
   32 | PUT(rsp) = t13
   33 | t38 = Sub64(t13,0x0000000000000080)
   34 | ====== AbiHint(0xt38, 128, t12) ======
   NEXT: PUT(rip) = t12; Ijk_Ret
}"
]

def exprBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4005bd, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t11 = GET:I64(rsp)
   03 | t10 = Sub64(t11,0x0000000000000008)
   04 | PUT(rsp) = t10
   05 | STle(t10) = t0
   06 | ------ IMark(0x4005be, 3, 0) ------
   07 | PUT(rbp) = t10
   08 | ------ IMark(0x4005c1, 4, 0) ------
   09 | t2 = Sub64(t10,0x0000000000000010)
   10 | PUT(rsp) = t2
   11 | PUT(rip) = 0x00000000004005c5
   12 | ------ IMark(0x4005c5, 7, 0) ------
   13 | t13 = LDle:I64(0x0000000000500030)
   14 | PUT(rip) = 0x00000000004005cc
   15 | ------ IMark(0x4005cc, 2, 0) ------
   16 | t15 = LDle:I32(t13)
   17 | t27 = 32Uto64(t15)
   18 | t14 = t27
   19 | PUT(rax) = t14
   20 | ------ IMark(0x4005ce, 3, 0) ------
   21 | t28 = 64to32(t14)
   22 | t16 = t28
   23 | PUT(cc_op) = 0x0000000000000007
   24 | t29 = 32Uto64(t16)
   25 | t18 = t29
   26 | PUT(cc_dep1) = t18
   27 | PUT(cc_dep2) = 0x000000000000000e
   28 | PUT(rip) = 0x00000000004005d1
   29 | ------ IMark(0x4005d1, 2, 0) ------
   30 | t32 = 64to32(t18)
   31 | t33 = 64to32(0x000000000000000e)
   32 | t31 = CmpEQ32(t32,t33)
   33 | t30 = 1Uto64(t31)
   34 | t25 = t30
   35 | t34 = 64to1(t25)
   36 | t20 = t34
   37 | if (t20) { PUT(rip) = 0x4005df; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004005d3; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4005d3, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004005d8
   03 | ------ IMark(0x4005d8, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004005dd
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400551) ======
   NEXT: PUT(rip) = 0x0000000000400551; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4005dd, 2, 0) ------
   NEXT: PUT(rip) = 0x0000000000400647; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4005df, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004005e4
   03 | ------ IMark(0x4005e4, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004005e9
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400551) ======
   NEXT: PUT(rip) = 0x0000000000400551; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I32 t14:Ity_I32 t15:Ity_I64 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I1 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I64 t30:Ity_I1 t31:Ity_I32 t32:Ity_I1

   00 | ------ IMark(0x4005e9, 4, 0) ------
   01 | t7 = GET:I64(rbp)
   02 | t6 = Add64(t7,0xfffffffffffffff0)
   03 | t8 = GET:I64(rax)
   04 | STle(t6) = t8
   05 | PUT(rip) = 0x00000000004005ed
   06 | ------ IMark(0x4005ed, 4, 0) ------
   07 | t9 = Add64(t7,0xfffffffffffffff0)
   08 | t11 = LDle:I64(t9)
   09 | PUT(rip) = 0x00000000004005f1
   10 | ------ IMark(0x4005f1, 2, 0) ------
   11 | t13 = LDle:I32(t11)
   12 | t26 = 32Uto64(t13)
   13 | t12 = t26
   14 | PUT(rax) = t12
   15 | ------ IMark(0x4005f3, 2, 0) ------
   16 | t27 = 64to32(t12)
   17 | t14 = t27
   18 | PUT(cc_op) = 0x0000000000000013
   19 | t28 = 32Uto64(t14)
   20 | t18 = t28
   21 | PUT(cc_dep1) = t18
   22 | PUT(cc_dep2) = 0x0000000000000000
   23 | PUT(rip) = 0x00000000004005f5
   24 | ------ IMark(0x4005f5, 2, 0) ------
   25 | t31 = 64to32(t18)
   26 | t30 = CmpEQ32(t31,0x00000000)
   27 | t29 = 1Uto64(t30)
   28 | t24 = t29
   29 | t32 = 64to1(t24)
   30 | t19 = t32
   31 | if (t19) { PUT(rip) = 0x4005f7; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400643; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x4005f7, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x00000000004005fe
   03 | ------ IMark(0x4005fe, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400600, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000000c
   16 | PUT(rip) = 0x0000000000400603
   17 | ------ IMark(0x400603, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000000c)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x400605; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400643; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x400605, 4, 0) ------
   01 | t5 = GET:I64(rbp)
   02 | t4 = Add64(t5,0xfffffffffffffff0)
   03 | t6 = LDle:I64(t4)
   04 | PUT(rax) = t6
   05 | PUT(rip) = 0x0000000000400609
   06 | ------ IMark(0x400609, 4, 0) ------
   07 | t7 = Add64(t5,0xfffffffffffffff8)
   08 | STle(t7) = t6
   09 | ------ IMark(0x40060d, 5, 0) ------
   10 | PUT(rdi) = 0x0000000000000005
   11 | PUT(rip) = 0x0000000000400612
   12 | ------ IMark(0x400612, 5, 0) ------
   13 | t12 = GET:I64(rsp)
   14 | t11 = Sub64(t12,0x0000000000000008)
   15 | PUT(rsp) = t11
   16 | STle(t11) = 0x0000000000400617
   17 | t13 = Sub64(t11,0x0000000000000080)
   18 | ====== AbiHint(0xt13, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x400617, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x40061b, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x0000000000400620
   08 | ------ IMark(0x400620, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x0000000000400625
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64

   00 | ------ IMark(0x400625, 4, 0) ------
   01 | t6 = GET:I64(rbp)
   02 | t5 = Add64(t6,0xfffffffffffffff0)
   03 | t7 = LDle:I64(t5)
   04 | PUT(rip) = 0x0000000000400629
   05 | ------ IMark(0x400629, 4, 0) ------
   06 | t8 = Add64(t6,0xfffffffffffffff8)
   07 | t10 = LDle:I64(t8)
   08 | PUT(rdx) = t10
   09 | PUT(rip) = 0x000000000040062d
   10 | ------ IMark(0x40062d, 4, 0) ------
   11 | t11 = Add64(t7,0x0000000000000008)
   12 | STle(t11) = t10
   13 | ------ IMark(0x400631, 5, 0) ------
   14 | PUT(rax) = 0x0000000000000000
   15 | PUT(rip) = 0x0000000000400636
   16 | ------ IMark(0x400636, 5, 0) ------
   17 | t16 = GET:I64(rsp)
   18 | t15 = Sub64(t16,0x0000000000000008)
   19 | PUT(rsp) = t15
   20 | STle(t15) = 0x000000000040063b
   21 | t17 = Sub64(t15,0x0000000000000080)
   22 | ====== AbiHint(0xt17, 128, 0x00000000004005bd) ======
   NEXT: PUT(rip) = 0x00000000004005bd; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I32 t6:Ity_I32 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I32 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I32 t26:Ity_I64 t27:Ity_I32 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64 t32:Ity_I32 t33:Ity_I64 t34:Ity_I32 t35:Ity_I64 t36:Ity_I64 t37:Ity_I64 t38:Ity_I64 t39:Ity_I64

   00 | ------ IMark(0x40063b, 4, 0) ------
   01 | t15 = GET:I64(rbp)
   02 | t14 = Add64(t15,0xfffffffffffffff0)
   03 | t16 = LDle:I64(t14)
   04 | PUT(rip) = 0x000000000040063f
   05 | ------ IMark(0x40063f, 4, 0) ------
   06 | t17 = Add64(t16,0x0000000000000010)
   07 | t19 = GET:I64(rax)
   08 | STle(t17) = t19
   09 | PUT(rip) = 0x0000000000400643
   10 | ------ IMark(0x400643, 4, 0) ------
   11 | t20 = Add64(t15,0xfffffffffffffff0)
   12 | t22 = LDle:I64(t20)
   13 | PUT(rax) = t22
   14 | PUT(rip) = 0x0000000000400647
   15 | ------ IMark(0x400647, 1, 0) ------
   16 | PUT(rsp) = t15
   17 | t4 = LDle:I64(t15)
   18 | PUT(rbp) = t4
   19 | t23 = Add64(t15,0x0000000000000008)
   20 | PUT(rsp) = t23
   21 | ------ IMark(0x400648, 2, 0) ------
   22 | PUT(rdx) = 0x0000000000000000
   23 | ------ IMark(0x40064a, 2, 0) ------
   24 | PUT(cc_op) = 0x0000000000000013
   25 | PUT(cc_dep1) = 0x0000000000000000
   26 | PUT(cc_dep2) = 0x0000000000000000
   27 | PUT(rdi) = 0x0000000000000000
   28 | PUT(rip) = 0x000000000040064c
   29 | ------ IMark(0x40064c, 1, 0) ------
   30 | t12 = LDle:I64(t23)
   31 | t13 = Add64(t23,0x0000000000000008)
   32 | PUT(rsp) = t13
   33 | t38 = Sub64(t13,0x0000000000000080)
   34 | ====== AbiHint(0xt38, 128, t12) ======
   NEXT: PUT(rip) = t12; Ijk_Ret
}"
]

def paren_exprBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x40064d, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t11 = GET:I64(rsp)
   03 | t10 = Sub64(t11,0x0000000000000008)
   04 | PUT(rsp) = t10
   05 | STle(t10) = t0
   06 | ------ IMark(0x40064e, 3, 0) ------
   07 | PUT(rbp) = t10
   08 | ------ IMark(0x400651, 4, 0) ------
   09 | t2 = Sub64(t10,0x0000000000000010)
   10 | PUT(rsp) = t2
   11 | PUT(rip) = 0x0000000000400655
   12 | ------ IMark(0x400655, 7, 0) ------
   13 | t13 = LDle:I64(0x0000000000500030)
   14 | PUT(rip) = 0x000000000040065c
   15 | ------ IMark(0x40065c, 2, 0) ------
   16 | t15 = LDle:I32(t13)
   17 | t27 = 32Uto64(t15)
   18 | t14 = t27
   19 | PUT(rax) = t14
   20 | ------ IMark(0x40065e, 3, 0) ------
   21 | t28 = 64to32(t14)
   22 | t16 = t28
   23 | PUT(cc_op) = 0x0000000000000007
   24 | t29 = 32Uto64(t16)
   25 | t18 = t29
   26 | PUT(cc_dep1) = t18
   27 | PUT(cc_dep2) = 0x0000000000000006
   28 | PUT(rip) = 0x0000000000400661
   29 | ------ IMark(0x400661, 2, 0) ------
   30 | t32 = 64to32(t18)
   31 | t33 = 64to32(0x0000000000000006)
   32 | t31 = CmpEQ32(t32,t33)
   33 | t30 = 1Uto64(t31)
   34 | t25 = t30
   35 | t34 = 64to1(t25)
   36 | t20 = t34
   37 | if (t20) { PUT(rip) = 0x400663; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040066f; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400663, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400668
   03 | ------ IMark(0x400668, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x000000000040066d
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x40066d, 2, 0) ------
   NEXT: PUT(rip) = 0x0000000000400679; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40066f, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400674
   03 | ------ IMark(0x400674, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400679
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400679, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040067e
   03 | ------ IMark(0x40067e, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400683
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004005bd) ======
   NEXT: PUT(rip) = 0x00000000004005bd; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I32 t12:Ity_I32 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I1 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I64 t27:Ity_I1 t28:Ity_I32 t29:Ity_I32 t30:Ity_I1

   00 | ------ IMark(0x400683, 4, 0) ------
   01 | t7 = GET:I64(rbp)
   02 | t6 = Add64(t7,0xfffffffffffffff8)
   03 | t8 = GET:I64(rax)
   04 | STle(t6) = t8
   05 | PUT(rip) = 0x0000000000400687
   06 | ------ IMark(0x400687, 7, 0) ------
   07 | t9 = LDle:I64(0x0000000000500030)
   08 | PUT(rip) = 0x000000000040068e
   09 | ------ IMark(0x40068e, 2, 0) ------
   10 | t11 = LDle:I32(t9)
   11 | t23 = 32Uto64(t11)
   12 | t10 = t23
   13 | PUT(rax) = t10
   14 | ------ IMark(0x400690, 3, 0) ------
   15 | t24 = 64to32(t10)
   16 | t12 = t24
   17 | PUT(cc_op) = 0x0000000000000007
   18 | t25 = 32Uto64(t12)
   19 | t14 = t25
   20 | PUT(cc_dep1) = t14
   21 | PUT(cc_dep2) = 0x0000000000000007
   22 | PUT(rip) = 0x0000000000400693
   23 | ------ IMark(0x400693, 2, 0) ------
   24 | t28 = 64to32(t14)
   25 | t29 = 64to32(0x0000000000000007)
   26 | t27 = CmpEQ32(t28,t29)
   27 | t26 = 1Uto64(t27)
   28 | t21 = t26
   29 | t30 = 64to1(t21)
   30 | t16 = t30
   31 | if (t16) { PUT(rip) = 0x400695; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004006a1; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400695, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040069a
   03 | ------ IMark(0x40069a, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x000000000040069f
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x40069f, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004006ab; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4006a1, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004006a6
   03 | ------ IMark(0x4006a6, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004006ab
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64

   00 | ------ IMark(0x4006ab, 4, 0) ------
   01 | t7 = GET:I64(rbp)
   02 | t6 = Add64(t7,0xfffffffffffffff8)
   03 | t8 = LDle:I64(t6)
   04 | PUT(rax) = t8
   05 | PUT(rip) = 0x00000000004006af
   06 | ------ IMark(0x4006af, 1, 0) ------
   07 | PUT(rsp) = t7
   08 | t2 = LDle:I64(t7)
   09 | PUT(rbp) = t2
   10 | t9 = Add64(t7,0x0000000000000008)
   11 | PUT(rsp) = t9
   12 | PUT(rip) = 0x00000000004006b0
   13 | ------ IMark(0x4006b0, 1, 0) ------
   14 | t4 = LDle:I64(t9)
   15 | t5 = Add64(t9,0x0000000000000008)
   16 | PUT(rsp) = t5
   17 | t10 = Sub64(t5,0x0000000000000080)
   18 | ====== AbiHint(0xt10, 128, t4) ======
   NEXT: PUT(rip) = t4; Ijk_Ret
}"
]

def statementBlocks : List String := [
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I32 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4006b1, 1, 0) ------
   01 | t0 = GET:I64(rbp)
   02 | t11 = GET:I64(rsp)
   03 | t10 = Sub64(t11,0x0000000000000008)
   04 | PUT(rsp) = t10
   05 | STle(t10) = t0
   06 | ------ IMark(0x4006b2, 3, 0) ------
   07 | PUT(rbp) = t10
   08 | ------ IMark(0x4006b5, 4, 0) ------
   09 | t2 = Sub64(t10,0x0000000000000010)
   10 | PUT(rsp) = t2
   11 | PUT(rip) = 0x00000000004006b9
   12 | ------ IMark(0x4006b9, 7, 0) ------
   13 | t13 = LDle:I64(0x0000000000500030)
   14 | PUT(rip) = 0x00000000004006c0
   15 | ------ IMark(0x4006c0, 2, 0) ------
   16 | t15 = LDle:I32(t13)
   17 | t27 = 32Uto64(t15)
   18 | t14 = t27
   19 | PUT(rax) = t14
   20 | ------ IMark(0x4006c2, 3, 0) ------
   21 | t28 = 64to32(t14)
   22 | t16 = t28
   23 | PUT(cc_op) = 0x0000000000000007
   24 | t29 = 32Uto64(t16)
   25 | t18 = t29
   26 | PUT(cc_dep1) = t18
   27 | PUT(cc_dep2) = 0x0000000000000002
   28 | PUT(rip) = 0x00000000004006c5
   29 | ------ IMark(0x4006c5, 2, 0) ------
   30 | t32 = 64to32(t18)
   31 | t33 = 64to32(0x0000000000000002)
   32 | t31 = CmpEQ32(t32,t33)
   33 | t30 = 1Uto64(t31)
   34 | t25 = t30
   35 | t34 = 64to1(t25)
   36 | t20 = t34
   37 | if (t20) { PUT(rip) = 0x4006c7; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400740; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4006c7, 5, 0) ------
   01 | PUT(rdi) = 0x0000000000000006
   02 | PUT(rip) = 0x00000000004006cc
   03 | ------ IMark(0x4006cc, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004006d1
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x4006d1, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x4006d5, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x00000000004006da
   08 | ------ IMark(0x4006da, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x00000000004006df
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4006df, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004006e4
   03 | ------ IMark(0x4006e4, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004006e9
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040064d) ======
   NEXT: PUT(rip) = 0x000000000040064d; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x4006e9, 4, 0) ------
   01 | t5 = GET:I64(rbp)
   02 | t4 = Add64(t5,0xfffffffffffffff0)
   03 | t6 = LDle:I64(t4)
   04 | PUT(rdx) = t6
   05 | PUT(rip) = 0x00000000004006ed
   06 | ------ IMark(0x4006ed, 4, 0) ------
   07 | t7 = Add64(t6,0x0000000000000008)
   08 | t9 = GET:I64(rax)
   09 | STle(t7) = t9
   10 | ------ IMark(0x4006f1, 5, 0) ------
   11 | PUT(rax) = 0x0000000000000000
   12 | PUT(rip) = 0x00000000004006f6
   13 | ------ IMark(0x4006f6, 5, 0) ------
   14 | t12 = GET:I64(rsp)
   15 | t11 = Sub64(t12,0x0000000000000008)
   16 | PUT(rsp) = t11
   17 | STle(t11) = 0x00000000004006fb
   18 | t13 = Sub64(t11,0x0000000000000080)
   19 | ====== AbiHint(0xt13, 128, 0x00000000004006b1) ======
   NEXT: PUT(rip) = 0x00000000004006b1; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4006fb, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rdx) = t9
   05 | PUT(rip) = 0x00000000004006ff
   06 | ------ IMark(0x4006ff, 4, 0) ------
   07 | t10 = Add64(t9,0x0000000000000010)
   08 | t12 = GET:I64(rax)
   09 | STle(t10) = t12
   10 | PUT(rip) = 0x0000000000400703
   11 | ------ IMark(0x400703, 7, 0) ------
   12 | t13 = LDle:I64(0x0000000000500030)
   13 | PUT(rip) = 0x000000000040070a
   14 | ------ IMark(0x40070a, 2, 0) ------
   15 | t15 = LDle:I32(t13)
   16 | t27 = 32Uto64(t15)
   17 | t14 = t27
   18 | PUT(rax) = t14
   19 | ------ IMark(0x40070c, 3, 0) ------
   20 | t28 = 64to32(t14)
   21 | t16 = t28
   22 | PUT(cc_op) = 0x0000000000000007
   23 | t29 = 32Uto64(t16)
   24 | t18 = t29
   25 | PUT(cc_dep1) = t18
   26 | PUT(cc_dep2) = 0x0000000000000001
   27 | PUT(rip) = 0x000000000040070f
   28 | ------ IMark(0x40070f, 6, 0) ------
   29 | t32 = 64to32(t18)
   30 | t33 = 64to32(0x0000000000000001)
   31 | t31 = CmpEQ32(t32,t33)
   32 | t30 = 1Uto64(t31)
   33 | t25 = t30
   34 | t34 = 64to1(t25)
   35 | t20 = t34
   36 | if (t20) { PUT(rip) = 0x400715; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64

   00 | ------ IMark(0x400715, 4, 0) ------
   01 | t5 = GET:I64(rbp)
   02 | t4 = Add64(t5,0xfffffffffffffff0)
   03 | t6 = LDle:I64(t4)
   04 | PUT(rip) = 0x0000000000400719
   05 | ------ IMark(0x400719, 6, 0) ------
   06 | STle(t6) = 0x00000007
   07 | ------ IMark(0x40071f, 5, 0) ------
   08 | PUT(rax) = 0x0000000000000000
   09 | PUT(rip) = 0x0000000000400724
   10 | ------ IMark(0x400724, 5, 0) ------
   11 | t9 = GET:I64(rsp)
   12 | t8 = Sub64(t9,0x0000000000000008)
   13 | PUT(rsp) = t8
   14 | STle(t8) = 0x0000000000400729
   15 | t10 = Sub64(t8,0x0000000000000080)
   16 | ====== AbiHint(0xt10, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400729, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040072e
   03 | ------ IMark(0x40072e, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400733
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004006b1) ======
   NEXT: PUT(rip) = 0x00000000004006b1; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64

   00 | ------ IMark(0x400733, 4, 0) ------
   01 | t3 = GET:I64(rbp)
   02 | t2 = Add64(t3,0xfffffffffffffff0)
   03 | t4 = LDle:I64(t2)
   04 | PUT(rdx) = t4
   05 | PUT(rip) = 0x0000000000400737
   06 | ------ IMark(0x400737, 4, 0) ------
   07 | t5 = Add64(t4,0x0000000000000018)
   08 | t7 = GET:I64(rax)
   09 | STle(t5) = t7
   10 | ------ IMark(0x40073b, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400740, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x0000000000400747
   03 | ------ IMark(0x400747, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400749, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000003
   16 | PUT(rip) = 0x000000000040074c
   17 | ------ IMark(0x40074c, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000003)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x40074e; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040078f; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40074e, 5, 0) ------
   01 | PUT(rdi) = 0x0000000000000008
   02 | PUT(rip) = 0x0000000000400753
   03 | ------ IMark(0x400753, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400758
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x400758, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x40075c, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x0000000000400761
   08 | ------ IMark(0x400761, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x0000000000400766
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400766, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040076b
   03 | ------ IMark(0x40076b, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400770
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040064d) ======
   NEXT: PUT(rip) = 0x000000000040064d; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x400770, 4, 0) ------
   01 | t5 = GET:I64(rbp)
   02 | t4 = Add64(t5,0xfffffffffffffff0)
   03 | t6 = LDle:I64(t4)
   04 | PUT(rdx) = t6
   05 | PUT(rip) = 0x0000000000400774
   06 | ------ IMark(0x400774, 4, 0) ------
   07 | t7 = Add64(t6,0x0000000000000008)
   08 | t9 = GET:I64(rax)
   09 | STle(t7) = t9
   10 | ------ IMark(0x400778, 5, 0) ------
   11 | PUT(rax) = 0x0000000000000000
   12 | PUT(rip) = 0x000000000040077d
   13 | ------ IMark(0x40077d, 5, 0) ------
   14 | t12 = GET:I64(rsp)
   15 | t11 = Sub64(t12,0x0000000000000008)
   16 | PUT(rsp) = t11
   17 | STle(t11) = 0x0000000000400782
   18 | t13 = Sub64(t11,0x0000000000000080)
   19 | ====== AbiHint(0xt13, 128, 0x00000000004006b1) ======
   NEXT: PUT(rip) = 0x00000000004006b1; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64

   00 | ------ IMark(0x400782, 4, 0) ------
   01 | t3 = GET:I64(rbp)
   02 | t2 = Add64(t3,0xfffffffffffffff0)
   03 | t4 = LDle:I64(t2)
   04 | PUT(rdx) = t4
   05 | PUT(rip) = 0x0000000000400786
   06 | ------ IMark(0x400786, 4, 0) ------
   07 | t5 = Add64(t4,0x0000000000000010)
   08 | t7 = GET:I64(rax)
   09 | STle(t5) = t7
   10 | ------ IMark(0x40078a, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I32 t11:Ity_I64 t12:Ity_I64 t13:Ity_I1 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I32 t22:Ity_I64 t23:Ity_I64 t24:Ity_I1 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x40078f, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x0000000000400796
   03 | ------ IMark(0x400796, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t20 = 32Uto64(t7)
   06 | t6 = t20
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400798, 2, 0) ------
   09 | t21 = 64to32(t6)
   10 | t8 = t21
   11 | PUT(cc_op) = 0x0000000000000013
   12 | t22 = 32Uto64(t8)
   13 | t12 = t22
   14 | PUT(cc_dep1) = t12
   15 | PUT(cc_dep2) = 0x0000000000000000
   16 | PUT(rip) = 0x000000000040079a
   17 | ------ IMark(0x40079a, 6, 0) ------
   18 | t25 = 64to32(t12)
   19 | t24 = CmpEQ32(t25,0x00000000)
   20 | t23 = 1Uto64(t24)
   21 | t18 = t23
   22 | t26 = 64to1(t18)
   23 | t13 = t26
   24 | if (t13) { PUT(rip) = 0x4007a0; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040082c; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4007a0, 5, 0) ------
   01 | PUT(rdi) = 0x0000000000000009
   02 | PUT(rip) = 0x00000000004007a5
   03 | ------ IMark(0x4007a5, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004007aa
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x4007aa, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x4007ae, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x00000000004007b3
   08 | ------ IMark(0x4007b3, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x00000000004007b8
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4007b8, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004007bd
   03 | ------ IMark(0x4007bd, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004007c2
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004006b1) ======
   NEXT: PUT(rip) = 0x00000000004006b1; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4007c2, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rdx) = t9
   05 | PUT(rip) = 0x00000000004007c6
   06 | ------ IMark(0x4007c6, 4, 0) ------
   07 | t10 = Add64(t9,0x0000000000000008)
   08 | t12 = GET:I64(rax)
   09 | STle(t10) = t12
   10 | PUT(rip) = 0x00000000004007ca
   11 | ------ IMark(0x4007ca, 7, 0) ------
   12 | t13 = LDle:I64(0x0000000000500030)
   13 | PUT(rip) = 0x00000000004007d1
   14 | ------ IMark(0x4007d1, 2, 0) ------
   15 | t15 = LDle:I32(t13)
   16 | t27 = 32Uto64(t15)
   17 | t14 = t27
   18 | PUT(rax) = t14
   19 | ------ IMark(0x4007d3, 3, 0) ------
   20 | t28 = 64to32(t14)
   21 | t16 = t28
   22 | PUT(cc_op) = 0x0000000000000007
   23 | t29 = 32Uto64(t16)
   24 | t18 = t29
   25 | PUT(cc_dep1) = t18
   26 | PUT(cc_dep2) = 0x0000000000000003
   27 | PUT(rip) = 0x00000000004007d6
   28 | ------ IMark(0x4007d6, 2, 0) ------
   29 | t32 = 64to32(t18)
   30 | t33 = 64to32(0x0000000000000003)
   31 | t31 = CmpEQ32(t32,t33)
   32 | t30 = 1Uto64(t31)
   33 | t25 = t30
   34 | t34 = 64to1(t25)
   35 | t20 = t34
   36 | if (t20) { PUT(rip) = 0x4007d8; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004007e4; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4007d8, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004007dd
   03 | ------ IMark(0x4007dd, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004007e2
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4007e2, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004007ee; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4007e4, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004007e9
   03 | ------ IMark(0x4007e9, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004007ee
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4007ee, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004007f3
   03 | ------ IMark(0x4007f3, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004007f8
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040064d) ======
   NEXT: PUT(rip) = 0x000000000040064d; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4007f8, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rdx) = t9
   05 | PUT(rip) = 0x00000000004007fc
   06 | ------ IMark(0x4007fc, 4, 0) ------
   07 | t10 = Add64(t9,0x0000000000000010)
   08 | t12 = GET:I64(rax)
   09 | STle(t10) = t12
   10 | PUT(rip) = 0x0000000000400800
   11 | ------ IMark(0x400800, 7, 0) ------
   12 | t13 = LDle:I64(0x0000000000500030)
   13 | PUT(rip) = 0x0000000000400807
   14 | ------ IMark(0x400807, 2, 0) ------
   15 | t15 = LDle:I32(t13)
   16 | t27 = 32Uto64(t15)
   17 | t14 = t27
   18 | PUT(rax) = t14
   19 | ------ IMark(0x400809, 3, 0) ------
   20 | t28 = 64to32(t14)
   21 | t16 = t28
   22 | PUT(cc_op) = 0x0000000000000007
   23 | t29 = 32Uto64(t16)
   24 | t18 = t29
   25 | PUT(cc_dep1) = t18
   26 | PUT(cc_dep2) = 0x000000000000000b
   27 | PUT(rip) = 0x000000000040080c
   28 | ------ IMark(0x40080c, 2, 0) ------
   29 | t32 = 64to32(t18)
   30 | t33 = 64to32(0x000000000000000b)
   31 | t31 = CmpEQ32(t32,t33)
   32 | t30 = 1Uto64(t31)
   33 | t25 = t30
   34 | t34 = 64to1(t25)
   35 | t20 = t34
   36 | if (t20) { PUT(rip) = 0x40080e; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040081d; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40080e, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400813
   03 | ------ IMark(0x400813, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400818
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x400818, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40081d, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400822
   03 | ------ IMark(0x400822, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400827
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x400827, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x40082c, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x0000000000400833
   03 | ------ IMark(0x400833, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400835, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x000000000000000b
   16 | PUT(rip) = 0x0000000000400838
   17 | ------ IMark(0x400838, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x000000000000000b)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x40083a; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400857; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x40083a, 5, 0) ------
   01 | PUT(rdi) = 0x000000000000000a
   02 | PUT(rip) = 0x000000000040083f
   03 | ------ IMark(0x40083f, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400844
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x400844, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x400848, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x000000000040084d
   08 | ------ IMark(0x40084d, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x0000000000400852
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x400852, 5, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I32 t3:Ity_I32 t4:Ity_I32 t5:Ity_I64 t6:Ity_I64 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I1 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I32 t21:Ity_I64 t22:Ity_I64 t23:Ity_I1 t24:Ity_I32 t25:Ity_I32 t26:Ity_I1

   00 | ------ IMark(0x400857, 7, 0) ------
   01 | t5 = LDle:I64(0x0000000000500030)
   02 | PUT(rip) = 0x000000000040085e
   03 | ------ IMark(0x40085e, 2, 0) ------
   04 | t7 = LDle:I32(t5)
   05 | t19 = 32Uto64(t7)
   06 | t6 = t19
   07 | PUT(rax) = t6
   08 | ------ IMark(0x400860, 3, 0) ------
   09 | t20 = 64to32(t6)
   10 | t8 = t20
   11 | PUT(cc_op) = 0x0000000000000007
   12 | t21 = 32Uto64(t8)
   13 | t10 = t21
   14 | PUT(cc_dep1) = t10
   15 | PUT(cc_dep2) = 0x0000000000000004
   16 | PUT(rip) = 0x0000000000400863
   17 | ------ IMark(0x400863, 2, 0) ------
   18 | t24 = 64to32(t10)
   19 | t25 = 64to32(0x0000000000000004)
   20 | t23 = CmpEQ32(t24,t25)
   21 | t22 = 1Uto64(t23)
   22 | t17 = t22
   23 | t26 = 64to1(t17)
   24 | t12 = t26
   25 | if (t12) { PUT(rip) = 0x400865; Ijk_Boring }
   NEXT: PUT(rip) = 0x00000000004008cd; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400865, 5, 0) ------
   01 | PUT(rdi) = 0x000000000000000a
   02 | PUT(rip) = 0x000000000040086a
   03 | ------ IMark(0x40086a, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x000000000040086f
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x40086f, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x400873, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x0000000000400878
   08 | ------ IMark(0x400878, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x000000000040087d
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x40087d, 2, 0) ------
   NEXT: PUT(rip) = 0x00000000004008b3; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64

   00 | ------ IMark(0x40087f, 4, 0) ------
   01 | t5 = GET:I64(rbp)
   02 | t4 = Add64(t5,0xfffffffffffffff0)
   03 | t6 = LDle:I64(t4)
   04 | PUT(rax) = t6
   05 | PUT(rip) = 0x0000000000400883
   06 | ------ IMark(0x400883, 4, 0) ------
   07 | t7 = Add64(t5,0xfffffffffffffff8)
   08 | STle(t7) = t6
   09 | ------ IMark(0x400887, 5, 0) ------
   10 | PUT(rdi) = 0x000000000000000b
   11 | PUT(rip) = 0x000000000040088c
   12 | ------ IMark(0x40088c, 5, 0) ------
   13 | t12 = GET:I64(rsp)
   14 | t11 = Sub64(t12,0x0000000000000008)
   15 | PUT(rsp) = t11
   16 | STle(t11) = 0x0000000000400891
   17 | t13 = Sub64(t11,0x0000000000000080)
   18 | ====== AbiHint(0xt13, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64

   00 | ------ IMark(0x400891, 4, 0) ------
   01 | t7 = GET:I64(rbp)
   02 | t6 = Add64(t7,0xfffffffffffffff0)
   03 | t8 = GET:I64(rax)
   04 | STle(t6) = t8
   05 | PUT(rip) = 0x0000000000400895
   06 | ------ IMark(0x400895, 4, 0) ------
   07 | t9 = Add64(t7,0xfffffffffffffff0)
   08 | t11 = LDle:I64(t9)
   09 | PUT(rip) = 0x0000000000400899
   10 | ------ IMark(0x400899, 4, 0) ------
   11 | t12 = Add64(t7,0xfffffffffffffff8)
   12 | t14 = LDle:I64(t12)
   13 | PUT(rdx) = t14
   14 | PUT(rip) = 0x000000000040089d
   15 | ------ IMark(0x40089d, 4, 0) ------
   16 | t15 = Add64(t11,0x0000000000000008)
   17 | STle(t15) = t14
   18 | ------ IMark(0x4008a1, 5, 0) ------
   19 | PUT(rax) = 0x0000000000000000
   20 | PUT(rip) = 0x00000000004008a6
   21 | ------ IMark(0x4008a6, 5, 0) ------
   22 | t20 = GET:I64(rsp)
   23 | t19 = Sub64(t20,0x0000000000000008)
   24 | PUT(rsp) = t19
   25 | STle(t19) = 0x00000000004008ab
   26 | t21 = Sub64(t19,0x0000000000000080)
   27 | ====== AbiHint(0xt21, 128, 0x00000000004006b1) ======
   NEXT: PUT(rip) = 0x00000000004006b1; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4008ab, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rdx) = t9
   05 | PUT(rip) = 0x00000000004008af
   06 | ------ IMark(0x4008af, 4, 0) ------
   07 | t10 = Add64(t9,0x0000000000000010)
   08 | t12 = GET:I64(rax)
   09 | STle(t10) = t12
   10 | PUT(rip) = 0x00000000004008b3
   11 | ------ IMark(0x4008b3, 7, 0) ------
   12 | t13 = LDle:I64(0x0000000000500030)
   13 | PUT(rip) = 0x00000000004008ba
   14 | ------ IMark(0x4008ba, 2, 0) ------
   15 | t15 = LDle:I32(t13)
   16 | t27 = 32Uto64(t15)
   17 | t14 = t27
   18 | PUT(rax) = t14
   19 | ------ IMark(0x4008bc, 3, 0) ------
   20 | t28 = 64to32(t14)
   21 | t16 = t28
   22 | PUT(cc_op) = 0x0000000000000007
   23 | t29 = 32Uto64(t16)
   24 | t18 = t29
   25 | PUT(cc_dep1) = t18
   26 | PUT(cc_dep2) = 0x0000000000000005
   27 | PUT(rip) = 0x00000000004008bf
   28 | ------ IMark(0x4008bf, 2, 0) ------
   29 | t32 = 64to32(t18)
   30 | t33 = 64to32(0x0000000000000005)
   31 | t31 = CmpEQ32(t32,t33)
   32 | t30 = 1Uto64(t31)
   33 | t25 = t30
   34 | t34 = 64to1(t25)
   35 | t20 = t34
   36 | if (t20) { PUT(rip) = 0x4008c1; Ijk_Boring }
   NEXT: PUT(rip) = 0x000000000040087f; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4008c1, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x00000000004008c6
   03 | ------ IMark(0x4008c6, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004008cb
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x4008cb, 2, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4008cd, 5, 0) ------
   01 | PUT(rdi) = 0x000000000000000c
   02 | PUT(rip) = 0x00000000004008d2
   03 | ------ IMark(0x4008d2, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x00000000004008d7
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x00000000004003fb) ======
   NEXT: PUT(rip) = 0x00000000004003fb; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64

   00 | ------ IMark(0x4008d7, 4, 0) ------
   01 | t4 = GET:I64(rbp)
   02 | t3 = Add64(t4,0xfffffffffffffff0)
   03 | t5 = GET:I64(rax)
   04 | STle(t3) = t5
   05 | ------ IMark(0x4008db, 5, 0) ------
   06 | PUT(rax) = 0x0000000000000000
   07 | PUT(rip) = 0x00000000004008e0
   08 | ------ IMark(0x4008e0, 5, 0) ------
   09 | t8 = GET:I64(rsp)
   10 | t7 = Sub64(t8,0x0000000000000008)
   11 | PUT(rsp) = t7
   12 | STle(t7) = 0x00000000004008e5
   13 | t9 = Sub64(t7,0x0000000000000080)
   14 | ====== AbiHint(0xt9, 128, 0x00000000004005bd) ======
   NEXT: PUT(rip) = 0x00000000004005bd; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I64 t8:Ity_I64 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I32 t16:Ity_I32 t17:Ity_I64 t18:Ity_I64 t19:Ity_I64 t20:Ity_I1 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I64 t25:Ity_I64 t26:Ity_I64 t27:Ity_I64 t28:Ity_I32 t29:Ity_I64 t30:Ity_I64 t31:Ity_I1 t32:Ity_I32 t33:Ity_I32 t34:Ity_I1

   00 | ------ IMark(0x4008e5, 4, 0) ------
   01 | t8 = GET:I64(rbp)
   02 | t7 = Add64(t8,0xfffffffffffffff0)
   03 | t9 = LDle:I64(t7)
   04 | PUT(rdx) = t9
   05 | PUT(rip) = 0x00000000004008e9
   06 | ------ IMark(0x4008e9, 4, 0) ------
   07 | t10 = Add64(t9,0x0000000000000008)
   08 | t12 = GET:I64(rax)
   09 | STle(t10) = t12
   10 | PUT(rip) = 0x00000000004008ed
   11 | ------ IMark(0x4008ed, 7, 0) ------
   12 | t13 = LDle:I64(0x0000000000500030)
   13 | PUT(rip) = 0x00000000004008f4
   14 | ------ IMark(0x4008f4, 2, 0) ------
   15 | t15 = LDle:I32(t13)
   16 | t27 = 32Uto64(t15)
   17 | t14 = t27
   18 | PUT(rax) = t14
   19 | ------ IMark(0x4008f6, 3, 0) ------
   20 | t28 = 64to32(t14)
   21 | t16 = t28
   22 | PUT(cc_op) = 0x0000000000000007
   23 | t29 = 32Uto64(t16)
   24 | t18 = t29
   25 | PUT(cc_dep1) = t18
   26 | PUT(cc_dep2) = 0x000000000000000b
   27 | PUT(rip) = 0x00000000004008f9
   28 | ------ IMark(0x4008f9, 2, 0) ------
   29 | t32 = 64to32(t18)
   30 | t33 = 64to32(0x000000000000000b)
   31 | t31 = CmpEQ32(t32,t33)
   32 | t30 = 1Uto64(t31)
   33 | t25 = t30
   34 | t34 = 64to1(t25)
   35 | t20 = t34
   36 | if (t20) { PUT(rip) = 0x4008fb; Ijk_Boring }
   NEXT: PUT(rip) = 0x0000000000400907; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x4008fb, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x0000000000400900
   03 | ------ IMark(0x400900, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400905
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x000000000040006f) ======
   NEXT: PUT(rip) = 0x000000000040006f; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64

   00 | ------ IMark(0x400905, 2, 0) ------
   NEXT: PUT(rip) = 0x0000000000400911; Ijk_Boring
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I64 t4:Ity_I64 t5:Ity_I64 t6:Ity_I64

   00 | ------ IMark(0x400907, 5, 0) ------
   01 | PUT(rax) = 0x0000000000000000
   02 | PUT(rip) = 0x000000000040090c
   03 | ------ IMark(0x40090c, 5, 0) ------
   04 | t4 = GET:I64(rsp)
   05 | t3 = Sub64(t4,0x0000000000000008)
   06 | PUT(rsp) = t3
   07 | STle(t3) = 0x0000000000400911
   08 | t5 = Sub64(t3,0x0000000000000080)
   09 | ====== AbiHint(0xt5, 128, 0x0000000000400000) ======
   NEXT: PUT(rip) = 0x0000000000400000; Ijk_Call
}",
  "IRSB {
   t0:Ity_I64 t1:Ity_I64 t2:Ity_I64 t3:Ity_I32 t4:Ity_I32 t5:Ity_I32 t6:Ity_I32 t7:Ity_I32 t8:Ity_I32 t9:Ity_I64 t10:Ity_I64 t11:Ity_I64 t12:Ity_I64 t13:Ity_I64 t14:Ity_I64 t15:Ity_I64 t16:Ity_I64 t17:Ity_I32 t18:Ity_I64 t19:Ity_I32 t20:Ity_I64 t21:Ity_I64 t22:Ity_I64 t23:Ity_I64 t24:Ity_I32 t25:Ity_I64 t26:Ity_I32 t27:Ity_I64 t28:Ity_I64 t29:Ity_I64 t30:Ity_I64 t31:Ity_I64

   00 | ------ IMark(0x400911, 4, 0) ------
   01 | t13 = GET:I64(rbp)
   02 | t12 = Add64(t13,0xfffffffffffffff0)
   03 | t14 = LDle:I64(t12)
   04 | PUT(rax) = t14
   05 | PUT(rip) = 0x0000000000400915
   06 | ------ IMark(0x400915, 1, 0) ------
   07 | PUT(rsp) = t13
   08 | t2 = LDle:I64(t13)
   09 | PUT(rbp) = t2
   10 | t15 = Add64(t13,0x0000000000000008)
   11 | PUT(rsp) = t15
   12 | ------ IMark(0x400916, 2, 0) ------
   13 | PUT(rdx) = 0x0000000000000000
   14 | ------ IMark(0x400918, 2, 0) ------
   15 | PUT(cc_op) = 0x0000000000000013
   16 | PUT(cc_dep1) = 0x0000000000000000
   17 | PUT(cc_dep2) = 0x0000000000000000
   18 | PUT(rdi) = 0x0000000000000000
   19 | PUT(rip) = 0x000000000040091a
   20 | ------ IMark(0x40091a, 1, 0) ------
   21 | t10 = LDle:I64(t15)
   22 | t11 = Add64(t15,0x0000000000000008)
   23 | PUT(rsp) = t11
   24 | t30 = Sub64(t11,0x0000000000000080)
   25 | ====== AbiHint(0xt30, 128, t10) ======
   NEXT: PUT(rip) = t10; Ijk_Ret
}"
]

def parserNTBlocks : List String :=
  termBlocks
  ++ sumBlocks
  ++ testBlocks
  ++ exprBlocks
  ++ paren_exprBlocks
  ++ statementBlocks


#guard
  (termBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  (sumBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  (testBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  (exprBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  (paren_exprBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  (statementBlocks.mapM (fun b => parseIRSB b)).isOk

#guard
  match parseProgram parserNTBlocks with
  | .ok _ => true
  | .error _ => false
