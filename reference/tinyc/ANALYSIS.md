# Tiny C Reference Compilation Analysis

## Build Environment

- **Flake:** `flake.nix` in this directory (pinned nixos-25.05)
- **Compiler:** GCC 14.3.0
- **Binutils:** GNU Binutils 2.44
- **Flags:** `gcc -c -O0 -o tiny.o tiny_orig.c`
- **Source:** Marc Feeley's Tiny-C compiler (from STALAGMITE subjects/tinyc/)
- **Built on:** abraxas (x86_64-linux), 2026-03-09

## Artifacts

- `tiny_orig.c` — source
- `tiny.o` — compiled object (ELF64, x86-64)
- `tiny_disasm.txt` — full `objdump -d` output (1166 lines)
- `flake.nix` + `flake.lock` — reproducible build environment

## next_sym() Instruction Profile

Function spans 0x6c–0x421 (950 bytes, ~230 instructions at -O0).

```
 88 mov        — register/memory moves (most are RIP-relative global access)
 23 jmp        — unconditional jumps (switch dispatch, loop back-edges)
 16 movl       — 32-bit immediate stores to memory (sym = TOKEN_VALUE)
 15 cmp        — character comparisons (ch == '{', ch >= '0', etc.)
 15 call       — calls to next_ch() and strcmp()
  6 lea        — address computation (int_val*10 pattern, array indexing)
  6 jle        — signed less-or-equal (range checks: ch <= '9', ch <= 'z')
  5 xor        — register zeroing (xor %eax,%eax before ret)
  5 add        — addition (pointer increment, int_val arithmetic)
  4 test       — zero tests (NULL check for words[], id_name[1] check)
  4 jg         — signed greater (range checks upper bound)
  4 je         — equal (exact char match: ch == '{')
  3 movslq     — sign-extend 32→64 (array index widening for words[sym])
  3 jne        — not-equal
  3 cltq       — sign-extend eax→rax (cdqe, same as movslq)
  1 sub        — stack frame setup
  1 shl        — shift left (int_val*10 = (val<<2+val)<<1 pattern)
  1 movzbl     — zero-extend byte→32 (movzx: reading id_name[1])
  1 movb       — byte store (id_name[i] = ch)
  1 jl         — signed less-than (never actually used in next_sym? check)
  1 ja         — unsigned above (possibly ch > 'z' check)
```

## next_ch() Instruction Profile

Function spans 0x34–0x6e (58 bytes, 17 instructions).

```
Key pattern:
  mov    0x0(%rip),%rax    — load &cursor (global pointer-to-pointer)
  mov    (%rax),%rax       — dereference: cursor value (*cursor)
  mov    (%rax),%rax       — dereference: **cursor (the pointer cursor points to)
  movzbl (%rax),%eax       — BYTE LOAD: read one byte from **cursor → zero-extend to 32-bit
  movsbl %al,%edx          — SIGN EXTEND: byte → signed int (for ch, which is `int`)
  mov    %edx,(%rax)       — store to global `ch`
  ... pointer increment (add $0x1 to *cursor) ...
```

## VEX ISA Gaps (Empirical)

### Required ops not yet in Lean:

| x86 instruction | pyvex op | Lean constructor needed | Notes |
|-----------------|----------|------------------------|-------|
| `movzbl (%rax),%eax` | `LDle:I8` + `Iop_8Uto32` | `load .w8` + `zext8to32` | **CRITICAL**: byte read in next_ch |
| `movsbl %al,%edx` | `Iop_8Sto32` | `sext8to32` (sign extend) | next_ch converts byte to int |
| `movb %cl,(%rdx,%rax,1)` | `STle(I8)` | `store .w8` | writing id_name[i] |
| `shl $0x2,%eax` | `Iop_Shl32` | `shl32` or use existing `shl64` + narrow | int_val*10 pattern |
| `cmp` + `jle`/`jg`/`ja` | various `CmpXX` | signed comparisons | range checks |
| `movslq %edx,%rdx` | `Iop_32Sto64` | `sext32to64` (sign extend) | array index widening |
| `test %rax,%rax` | `Iop_CmpEQ64` with 0 | already have eq64 | NULL pointer check |
| `call strcmp` | external call | **STUB NEEDED** | keyword matching loop |

### Required ops already in Lean:

| x86 instruction | pyvex op | Lean constructor |
|-----------------|----------|-----------------|
| `mov` (reg-reg) | `Get`/`Put` | `get`/`put` |
| `mov` (mem load 64) | `LDle:I64` | `load64` (→ `load .w64`) |
| `mov` (mem store 64) | `STle(I64)` | `store64` (→ `store .w64`) |
| `add` | `Iop_Add64`/`Iop_Add32` | `add64`/`add32` |
| `sub` | `Iop_Sub64` | `sub64` |
| `xor` | `Iop_Xor64` | `xor64` |
| `cmp` + `je` | `Iop_CmpEQ64` | `eq64` |
| `lea` | `Iop_Add64` | `add64` |

### Register gaps:

next_sym uses: rax, rbp, rcx, rdx, rsi, rdi, rip + eflags
next_ch uses: rax, rbp, rdx, rip

**Currently supported:** rax, rcx, rdi, rip + cc fields (8 total)
**Need to add:** rdx, rsi, rbp, rsp (minimum for next_sym)

### The strcmp problem:

next_sym calls `strcmp(words[sym], id_name)` in a loop for keyword matching.
This is the ONE external call. Options:
1. Stub it (SimProcedure-style summary in Lean)
2. Inline it (compile strcmp into the binary, analyze everything)
3. Skip keyword path initially (analyze only the single-char dispatch)

Option 3 is pragmatic for first milestone: the single-char dispatch (punctuation,
digits, single letter IDs) exercises the full pipeline without needing stubs.

## int_val*10 Pattern

GCC -O0 compiles `int_val = int_val*10 + (ch - '0')` as:
```
shl    $0x2,%eax      ; val * 4
add    %edx,%eax      ; val * 4 + val = val * 5
add    %eax,%eax      ; (val * 5) * 2 = val * 10
```

No `imul` needed! This is `shl` + two `add` instructions. All available
(shl64 exists, add32/add64 exist).

## Conclusion

The ISA gap is smaller than expected:
1. **load8 + sign/zero extend** — the critical blocker (width refactor handles load8)
2. **Sign extension ops** (8→32, 32→64) — new, but mechanical
3. **4 more registers** (rdx, rsi, rbp, rsp) — mechanical Fintype extension
4. **strcmp stub** — can defer by targeting non-keyword path first
5. **store8** — for id_name writes, part of width refactor

Everything else (cmp, jcc patterns) maps to existing ops via pyvex
flag computation → amd64CalculateCondition or direct comparison ops.
