# VEX Opcode / IR Coverage Report

This report inventories the current Lean VEX slice against the generated fixture corpus and the
pinned `angr`/`pyvex` extractor support.

## Current Lean Surface

```text
Category   Supported constructors / ops
---------  -----------------------------------------------------------------
Reg        rax, rcx, rdi, rip, cc_op, cc_dep1, cc_dep2, cc_ndep
Expr       const, get, tmp, narrow32, zext64, add32, add64, sub64,
           xor64, and64, or64, shl64, shr64, load64
Cond       eq64, lt64, le64, amd64CalculateCondition
Stmt       wrTmp, put, store64, exit
```

## Extractor-Supported pyvex Shapes

```text
Kind                 Supported now
-------------------  ---------------------------------------------------------
pyvex expr classes   Binop, Const, Get, Load, RdTmp
pyvex stmt classes   Exit, IMark, Put, Store, WrTmp
expr binops          Iop_Add32, Iop_Add64, Iop_Sub64, Iop_Xor64,
                     Iop_And64, Iop_Or64, Iop_Shl64, Iop_Shr64
condition binops     Iop_CmpEQ32, Iop_CmpEQ64, Iop_CmpLT64U, Iop_CmpLE64U
condition helpers    amd64g_calculate_condition
lowered expr tags    const, get, load64, tmp, narrow32, zext64,
                     add32, add64, sub64, xor64, and64, or64, shl64, shr64
lowered stmt tags    put, wrtmp, store64, exit
```

## Corpus Inventory

```text
Fixture count  39
```

### Statement tag counts

```text
Stmt tag   Count
---------  -----
wrtmp        136
put           77
exit          18
store64        1
```

### Expression / condition tag counts

```text
Expr / cond tag              Count
---------------------------  -----
tmp                            161
get                             69
const                           50
add32                            5
add64                           16
sub64                            1
xor64                            1
and64                            1
or64                             1
shl64                            2
shr64                            2
narrow32                        16
zext64                          15
low32                            2
uext32                           2
cond:eq64                       12
cond:lt64                        2
cond:le64                        2
cond:amd64CalculateCondition     2
load64                           1
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
amd64_mov_rcx_rdi.json
amd64_mov_rdi_rcx.json
amd64_or_rax_rdi.json
amd64_shl_rax_3.json
amd64_shr_rax_4.json
amd64_sub_rax_rdi.json
amd64_xor_rax_rdi.json
```

## Effective Coverage Summary

```text
Layer              Covered now                           Notes
-----------------  ------------------------------------  -----------------------------------------------
Registers          rax, rcx, rdi, rip + cc regs         still a tiny architectural slice
Data movement      GET, PUT, tmp flow                   straight-line register transfer
Arithmetic         Add32/Add64/Sub64 + bitwise/shifts   direct byte-backed fixtures now present
Memory reads       LDle:I64                             proved in Lean, cross-checked against angr
Memory writes      STle with 64-bit data                proved in Lean, cross-checked against angr
Branch conditions  Eq64, LT64U, LE64U, amd64 helper     direct exits plus the current jz helper slice
CFG shape          fallthrough + single guarded exit    not multi-block, not general CFG
```

## Hand-Authored Edge Cases

```text
Module                         Covered semantics
----------------------------   --------------------------------------------------------------
VexOpcodeEdgeCases.lean        narrow32/zext64 mask to low 32 bits
                               add32 wraps modulo 2^32 and zero-extends
                               shl64/shr64 mask shift counts with 0x3F
                               lt64/le64 are unsigned comparisons
```

## Supported Raw VEX IR Patterns

```text
VEX concept            Supported form now
--------------------   ------------------------------------------------------
WrTmp                  yes
Put                    yes
Exit                   yes, equality, unsigned lt/le, and one amd64 helper
Load                   yes, LDle:I64
Store                  yes, STle(I64 payload)
Binop arithmetic       Add32, Add64, Sub64, Xor64, And64, Or64, Shl64, Shr64
Binop comparison       CmpEQ32, CmpEQ64, CmpLT64U, CmpLE64U
Flag helper            amd64g_calculate_condition (current zero-condition slice)
Temps                  yes, via WrTmp / RdTmp
IMark                  parsed/observed, not semantically interesting itself
```

## Not Yet Covered

```text
Arithmetic / bitwise   Iop_Sar64 and the wider arithmetic/bitwise families
Comparisons            CmpNE*, signed families, wider unsigned families
Memory widths          anything other than 64-bit little-endian load/store
Casts / width changes  sign extension, zero extension, truncation
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
1. Byte-width memory path: load8 plus reviewed width design
2. Signed operations: Sar64 and signed comparison families
3. More flags/helper coverage beyond the current zero-condition slice
4. Wider register coverage before general CFG/control-flow work
```
