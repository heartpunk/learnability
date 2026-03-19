# New Subject Status (2026-03-19)

## Bytecode Interpreters

### Lua 5.4 (luaV_execute)
- **Status**: PARSES, hangs in stabilization
- Source: `nix build .#lua-obj` → `reference/lua/blocks_lvm.json`
- 774 blocks, 1120 body branches, 7 projected registers
- Projection: [rax, fs_base, xmm0, rsi, rbp, rsp, rdi]
- VEX gaps fixed: I32StoF64 (1-arg), Add64F0x2, CmpLT64S, Sub8
- Stabilization hangs: 1120 branches × frontier is too large for current
  composition performance

### QuickJS (JS_CallInternal)
- **Status**: PARSES, hangs in stabilization
- Source: `nix build .#quickjs-obj` → `reference/quickjs/blocks_core.json`
- 1348 blocks, 1688 body branches
- VEX gaps fixed: r10, r13-r15 register mapping
- Stabilization hangs: 1688 branches × frontier is too large

## Terminal Emulators

### libtsm (parse_data)
- **Status**: Extracted, blocks.json needs regeneration (jj state loss)
- Source: `nix build .#libtsm-obj` → VEX extract
- 201 functions, 636 branches for parse_data
- Previously ran successfully with terminal-subjects agent

### st (csihandle, tputc, eschandle)
- **Status**: Extracted, blocks.json needs regeneration
- Source: `nix build .#st-obj` → VEX extract
- tputc needed CmpEQ16 (now fixed)
- 85 functions

### libvte (feed_to_state)
- **Status**: Extracted, needs pre-filtered blocks_parser.json
- Source: `nix build .#libvte-obj` → VEX extract
- 3365 functions total, pre-filter to ~6 parser functions
- C++ template bloat makes full analysis impractical

## VEX Parser Improvements Made

1. CmpEQ16, CmpNE16, CmpNE8
2. 1-arg variants of I32StoF64, I64StoF64, F64toI32S, etc.
3. Add64F0x2, Sub64F0x2, Mul64F0x2, Div64F0x2 (alternate SIMD naming)
4. CmpLT64S (signed 64-bit less-than)
5. Sub8 (8-bit subtraction)
6. r10, r13-r15 register mapping

## Bottleneck

Large interpreter functions (1000+ body branches) overwhelm the stabilization
loop. The composition of 1000+ branches with the frontier, followed by
simplification and dedup, doesn't complete within minutes. This is the same
class of issue as cgi_decode's init_hex_values but at a larger scale.

The SymMem map representation and/or hash-consing would help. A per-function
complexity cap (skip functions with >500 body branches) would be the pragmatic
workaround.
