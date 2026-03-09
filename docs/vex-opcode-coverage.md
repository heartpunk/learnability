# VEX Opcode / IR Coverage Report

This report inventories the current Lean VEX slice against the generated fixture corpus and the
pinned `angr`/`pyvex` extractor support.

## Current Lean Surface

```text
Category   Supported constructors / ops
---------  -----------------------------------------------------------------
Width      w8, w16, w32, w64
Reg        rax, rcx, rdi, rip, cc_op, cc_dep1, cc_dep2, cc_ndep
Expr       const, get, tmp, narrow32, zext64, add32, sub32, add64, sub64,
           xor64, and64, or64, shl32, shl64, shr64, sext8to32, sext32to64, load
Cond       eq64, lt64, le64, amd64CalculateCondition
Stmt       wrTmp, put, store, exit
```

## Extractor-Supported pyvex Shapes

```text
Kind                 Supported now
-------------------  ---------------------------------------------------------
pyvex expr classes   Binop, Const, Get, Load, RdTmp
pyvex stmt classes   Exit, IMark, Put, Store, WrTmp
expr unops           Iop_64to32, Iop_32Uto64, Iop_8Sto32, Iop_32Sto64,
                     selected 8U/16U widenings collapsed by the extractor
expr binops          Iop_Add32, Iop_Sub32, Iop_Add64, Iop_Sub64, Iop_Xor64,
                     Iop_And64, Iop_Or64, Iop_Shl32, Iop_Shl64, Iop_Shr64
condition binops     Iop_CmpEQ32, Iop_CmpEQ64, Iop_CmpLT64U, Iop_CmpLE64U
condition helpers    amd64g_calculate_condition
load widths          Ity_I8, Ity_I16, Ity_I32, Ity_I64
store widths         8, 16, 32, 64-bit little-endian payloads
lowered expr tags    const, get, load:w8/w16/w32/w64, tmp, narrow32, zext64,
                     sext8to32, sext32to64, add32, sub32, add64, sub64, xor64, and64, or64, shl32, shl64, shr64
lowered stmt tags    put, wrtmp, store:w8/w16/w32/w64, exit
```

## Corpus Inventory

```text
Fixture count  45
```

### Statement tag counts

```text
Stmt tag   Count
---------  -----
wrtmp        162
put           88
exit          18
store:w64      1
store:w8       1
```

### Expression / condition tag counts

```text
Expr / cond tag              Count
---------------------------  -----
tmp                            195
get                             77
const                           53
add32                            5
sub32                            1
add64                           16
sub64                            1
xor64                            1
and64                            1
or64                             1
shl32                            1
shl64                            2
shr64                            2
narrow32                        22
zext64                          24
sext8to32                        1
sext32to64                       1
cond:eq64                       12
cond:lt64                        2
cond:le64                        2
cond:amd64CalculateCondition     2
load:w8                          2
load:w64                         1
```

### Fixture inventory

```text
amd64_add_eax_edi.json
amd64_add_eax_edi_jz_fallthrough.json
amd64_add_eax_edi_jz_taken.json
amd64_and_rax_rdi.json
amd64_cmp_rax_rdi_jb_fallthrough.json
amd64_cmp_rax_rdi_jb_taken.json
amd64_cmp_rax_rdi_jbe_fallthrough.json
amd64_cmp_rax_rdi_jbe_taken.json
amd64_jrcxz_skip_lea_fallthrough.json
amd64_jrcxz_skip_lea_rax_rdi_plus_rcx_fallthrough.json
amd64_jrcxz_skip_lea_rax_rdi_plus_rcx_taken.json
amd64_jrcxz_skip_lea_rcx_rdi_plus_5_fallthrough.json
amd64_jrcxz_skip_lea_rcx_rdi_plus_5_taken.json
amd64_jrcxz_skip_lea_rdi_rdi_plus_8_fallthrough.json
amd64_jrcxz_skip_lea_rdi_rdi_plus_8_taken.json
amd64_jrcxz_skip_lea_taken.json
amd64_jrcxz_skip_mov_rax_rdi_fallthrough.json
amd64_jrcxz_skip_mov_rax_rdi_taken.json
amd64_jz_only_fallthrough.json
amd64_jz_only_taken.json
amd64_lea_eax_rdi_plus_5.json
amd64_lea_ecx_rdi_plus_5.json
amd64_lea_rax_rcx_plus_5.json
amd64_lea_rax_rdi.json
amd64_lea_rax_rdi_plus_rcx.json
amd64_lea_rax_rdi_plus_rcx_plus_8.json
amd64_lea_rcx_rdi_plus_5.json
amd64_lea_rdi_plus_5.json
amd64_mov_eax_edi.json
amd64_mov_ecx_edi.json
amd64_mov_mem_rdi_rax.json
amd64_mov_rax_mem_rdi.json
amd64_movslq_rax_edi.json
amd64_movsx_eax_mem_rdi.json
amd64_movzx_rax_mem_rdi.json
amd64_mov_rcx_rdi.json
amd64_mov_rdi_rcx.json
amd64_or_rax_rdi.json
amd64_shl_rax_3.json
amd64_shl_eax_2.json
amd64_shr_rax_4.json
amd64_sub_eax_edi.json
amd64_sub_rax_rdi.json
amd64_xor_rax_rdi.json
```

## Effective Coverage Summary

```text
Layer              Covered now                           Notes
-----------------  ------------------------------------  ---------------------------------------------------------
Registers          rax, rcx, rdi, rip + cc regs         still a tiny architectural slice
Data movement      GET, PUT, tmp flow                   straight-line register transfer
Arithmetic         Add32/Sub32/Add64/Sub64 + shifts     direct byte-backed fixtures now present
Casts / width      narrow32/zext64/sext8to32/sext32to64 direct byte-backed fixtures now present for signed widening
Memory reads       load .w8/.w16/.w32/.w64 semantics    core semantics are generic; corpus now uses w8 and w64
Memory writes      store .w8/.w16/.w32/.w64 semantics   core semantics are generic; corpus uses w8 and w64
Branch conditions  Eq64, LT64U, LE64U, amd64 helper     direct exits plus the current jz helper slice
CFG shape          fallthrough + single guarded exit    not multi-block, not general CFG
```

## Hand-Authored Edge Cases

```text
Module                         Covered semantics
----------------------------   --------------------------------------------------------------
VexOpcodeEdgeCases.lean        narrow32/zext64 mask to low 32 bits
                               sext8to32 preserves the signed low-byte 32-bit pattern
                               sext32to64 sign-extends the signed low 32-bit pattern
                               add32/sub32 wrap modulo 2^32 and zero-extend
                               shl32 masks shift counts with 0x1F and shifts truncated bits
                               shl64/shr64 mask shift counts with 0x3F
                               load/store widths preserve little-endian low-byte slices
                               load .w8 zero-fills missing bytes
                               lt64/le64 are unsigned comparisons
```

## Supported Raw VEX IR Patterns

```text
VEX concept            Supported form now
--------------------   ------------------------------------------------------
WrTmp                  yes
Put                    yes
Exit                   yes, equality, unsigned lt/le, and one amd64 helper
Load                   yes, LDle:I8/I16/I32/I64
Store                  yes, STle with 8/16/32/64-bit payloads
Unops / casts          64to32, 32Uto64, 8Sto32, 32Sto64, selected collapsed 8U/16U widenings
Binop arithmetic       Add32, Sub32, Add64, Sub64, Xor64, And64, Or64, Shl32, Shl64, Shr64
Binop comparison       CmpEQ32, CmpEQ64, CmpLT64U, CmpLE64U
Flag helper            amd64g_calculate_condition (current zero-condition slice)
Temps                  yes, via WrTmp / RdTmp
IMark                  parsed/observed, not semantically interesting itself
```

## Not Yet Covered

```text
Arithmetic / bitwise   Iop_Sar64 and the wider arithmetic/bitwise families
Comparisons            CmpNE*, signed families, wider unsigned families
Memory fixtures        dedicated byte-backed w16/w32 loads and non-w64 stores
Width changes          remaining sign/zero extension and truncation families beyond the current slice
Flags / helpers        broader ccall helpers and flag computation machinery
Effects                Dirty helpers, CAS, atomics
Control flow           indirect jumps, calls, returns, multi-block CFG
Expressions            ITE and richer expression surface
Registers              everything beyond rax/rcx/rdi/rip and the current cc regs
Architectures          everything beyond AMD64
```

## Turing-Completeness Status

No. This slice is not Turing complete.

```text
Reason
---------------------------------------------------------
No multi-block semantics
No general loop / back-edge model in the VEX frontend
No indirect control flow
Tiny expression and statement fragment
Tiny architectural register slice
```

## Immediate Next Coverage Targets

```text
1. 32-bit shift-left support for the `int_val * 10` path
2. Byte-backed `store .w8` coverage
3. Byte-backed w16/w32 memory fixtures
4. Signed operations: Sar64 and signed comparison families
```
