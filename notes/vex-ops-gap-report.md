# VEX IR Operations Gap Report

Generated 2026-03-16 from all 8 stalagmite subjects.

## Summary

| Subject | Functions | Failing | Success Rate |
|---------|-----------|---------|--------------|
| cgi_decode | 4 | 3 | 25% |
| calc | 15 | 10 | 33% |
| lisp | 21 | 7 | 67% |
| json | 19 | 11 | 42% |
| cjson | 152 | 84 | 45% |
| parson | 151 | 48 | 68% |
| simplearithmeticparser | 82 | 39 | 52% |
| mjs | 410 | 239 | 42% |
| **TOTAL** | **854** | **441** | **48%** |

441 of 854 functions fail to parse. Fixing 4 categories (missing registers, 64to8, 1Uto8, And32) would recover the majority.

---

## Category 1: Missing Registers (339 function failures, ~77% of all failures)

### 1a. `unknown register: fs` — 115 hits across 7/8 subjects

**Subjects:** calc(6), lisp(3), json(3), cjson(11), parson(14), simplearithmeticparser(4), mjs(74)

**Semantics:** `fs` is the x86-64 FS segment register base. On Linux, `fs_base` points to the thread-local storage (TLS) area. GCC/clang emit `mov rax, fs:[0x28]` for stack canary reads. Almost every non-trivial function touches it for stack protector code.

**What to change:**
- `VexAmd64.lean`: Add `| r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | fs_base` to `Amd64Reg`
- `VexIRParser.lean` `resolveReg`: Add `"fs" | "fs_base" => .ok .fs_base`
- Update `Fintype`, `EnumReg`, `Hashable`, `Repr`, `mkAmd64State*` instances

**Difficulty:** Easy (mechanical additions, but ripples through many files due to Fintype/pattern-match exhaustiveness)

### 1b. `unknown register: r8` — 78 hits across 5/8 subjects

**Subjects:** cjson(18), parson(5), simplearithmeticparser(4), mjs(51)

**Semantics:** 5th argument register in the System V AMD64 ABI. Any function that calls a 5+ argument function or uses r8 as a scratch register hits this.

**What to change:** Same as 1a — add `r8` (and sub-regs `r8d`, `r8w`, `r8b`) to `Amd64Reg` enum and `resolveReg`.

**Difficulty:** Easy

### 1c. `unknown register: rbx` — 59 hits across 7/8 subjects

**Subjects:** lisp(4), json(2), cjson(8), parson(3), simplearithmeticparser(16), mjs(26)

**Semantics:** Callee-saved general-purpose register. Used by any function that needs to preserve values across calls. Very common in compiled C/C++.

**What to change:** Same pattern — add to `Amd64Reg` and `resolveReg`. Map `rbx|ebx|bx|bl|bh`.

**Difficulty:** Easy

### 1d. `unknown register: xmm0lq` / `xmm0` — 24 hits across 3/8 subjects

**Subjects:** cjson(4+1), parson(7+1), mjs(10+1)

**Semantics:** SSE/floating-point register. `xmm0lq` = low 64-bit quadword of xmm0. Used for `double` parameters/returns per AMD64 ABI. Appears in any code that handles floating-point (JSON number parsing, `cJSON_SetNumberHelper`, etc.).

**What to change:** Add `xmm0` (and potentially xmm1-xmm7) to `Amd64Reg`. The `lq` suffix is a pyvex-ism for the low quadword — `resolveReg` should map `xmm0lq|xmm0` to the same register. Semantically, floating-point ops need new `Expr` constructors or an abstract treatment (opaque values).

**Difficulty:** Medium (register addition is easy, but floating-point semantics need design decisions — treat as opaque/abstract, or model IEEE754?)

### 1e. `unknown register: r9` — 12 hits, mjs only

**Semantics:** 6th argument register (System V). Same treatment as r8.

**Difficulty:** Easy

### 1f. `unknown register: r12` — 8 hits across 2/8 subjects

**Subjects:** simplearithmeticparser(7), mjs(1)

**Semantics:** Callee-saved register. Same treatment as rbx.

**Difficulty:** Easy

### 1g. `unknown register: r11` — 1 hit (cgi_decode)

**Semantics:** Scratch/temporary register clobbered by syscalls.

**Difficulty:** Easy

### 1h. `unknown register: ymm0` — 1 hit (mjs)

**Semantics:** 256-bit AVX extension of xmm0. Appears in `ffi_set_float`. Would need AVX register modeling.

**Difficulty:** Hard (AVX semantics are complex; could treat as opaque for now)

---

## Category 2: Unsupported Expressions — Narrow/Widen Operations (63 hits)

### 2a. `64to8(...)` — 34 hits across 6/8 subjects

**Subjects:** cgi_decode(2), calc(2), json(1), cjson(12), parson(10), mjs(18 — 7 with tmp args, 11 with const args)

**Semantics:** Truncate a 64-bit value to 8 bits. VEX IR `Iop_64to8`. Used for byte stores (`STle` with byte value), character comparisons, and byte manipulation.

Two variants:
- `64to8(0xNN)` — constant truncation (trivially simplifiable at parse time)
- `64to8(tN)` — dynamic truncation (needs `.narrow8` or just mask to 0xFF)

**What to change:**
- `VexSyntax.lean`: Add `| narrow8 : Expr Reg -> Expr Reg` to `Expr` (or reuse `.load .w8` / mask)
- `VexIRParser.lean` `parseExpr`: Add `| "64to8", [a] => do let e <- parseExpr a st fuel; .ok (.narrow8 e)`
- Alternative: Since the pipeline ultimately cares about 64-bit register values, `64to8` on a constant can just mask to `0xFF` at parse time, and on a tmp can be treated as identity (the store width handles truncation).

**Difficulty:** Trivial if treated as identity/mask; Easy if adding a proper `narrow8` constructor

### 2b. `1Uto8(...)` — 26 hits across 3/8 subjects

**Subjects:** cjson(9), simplearithmeticparser(6), mjs(11)

**Semantics:** Zero-extend a 1-bit boolean to 8 bits. VEX IR `Iop_1Uto8`. Used for boolean-to-byte conversions (e.g., `cJSON_IsTrue` returning a bool as a byte).

**What to change:** The parser already handles `1Uto64` and `1Uto32` as identity (pass-through). Add the same for `1Uto8`:
- `VexIRParser.lean` `parseExpr`: Add `| "1Uto8", [a] => parseExpr a st fuel`

**Difficulty:** Trivial (one line in `parseExpr`)

### 2c. `8Sto64(...)` — 3 hits across 2/8 subjects

**Subjects:** json(2), mjs(1)

**Semantics:** Sign-extend an 8-bit value to 64 bits. VEX IR `Iop_8Sto64`. Used in `isspace_`/`iscntrl_` type functions and string processing.

**What to change:**
- `VexSyntax.lean`: Add `| sext8to64 : Expr Reg -> Expr Reg` or compose as `sext32to64 (sext8to32 e)`
- `VexIRParser.lean`: Add `| "8Sto64", [a] => do let e <- parseExpr a st fuel; .ok (.sext32to64 (.sext8to32 e))`

**Difficulty:** Trivial (compose existing constructors)

---

## Category 3: Unsupported Expressions — 32-bit ALU Operations (27 hits)

### 3a. `And32(...)` — 16 hits across 3/8 subjects

**Subjects:** cjson(4), parson(2), mjs(10)

**Semantics:** Bitwise AND on 32-bit values. VEX IR `Iop_And32`. Used for flag testing (`val & 0x100`), mask operations, etc.

**What to change:**
- `VexSyntax.lean`: Add `| and32 : Expr Reg -> Expr Reg -> Expr Reg`
- `VexIRParser.lean`: Add case in `parseExpr`
- Eval in `VexCompTree.lean` or wherever `evalExpr` lives: `mask32 (a &&& b)`

**Difficulty:** Easy (follows existing pattern of `add32`/`sub32`/`shl32`)

### 3b. `Or32(...)` — 5 hits across 2/8 subjects

**Subjects:** parson(1), mjs(4)

**Semantics:** Bitwise OR on 32-bit values. Same as 3a but OR.

**What to change:** Add `| or32 : Expr Reg -> Expr Reg -> Expr Reg` following same pattern.

**Difficulty:** Easy

### 3c. `Xor32(...)` — 4 hits across 2/8 subjects

**Subjects:** cjson(3), simplearithmeticparser(1)

**Semantics:** Bitwise XOR on 32-bit values. Already supported at 64-bit level (`xor64`).

**What to change:** Add `| xor32 : Expr Reg -> Expr Reg -> Expr Reg`

**Difficulty:** Easy

### 3d. `Not32(...)` — 1 hit (mjs)

**Semantics:** Bitwise NOT on 32-bit value. One's complement.

**What to change:** Add `| not32 : Expr Reg -> Expr Reg`, eval as `mask32 (~~~a)`

**Difficulty:** Easy

### 3e. `Mul32(...)` — 1 hit (calc)

**Semantics:** 32-bit multiplication. Used by calculator `mult_func`.

**What to change:** Add `| mul32 : Expr Reg -> Expr Reg -> Expr Reg`, eval as `mask32 (a * b)`

**Difficulty:** Easy

### 3f. `Sar32(...)` — 1 hit (calc)

**Semantics:** Arithmetic (signed) right shift on 32-bit value. Used in `div_func` (sign extension for division).

**What to change:** Add `| sar32 : Expr Reg -> Expr Reg -> Expr Reg`. Eval requires sign-extension logic: shift the sign-extended 32-bit value right, then mask to 32.

**Difficulty:** Easy-Medium (needs signed shift semantics, but straightforward)

---

## Category 4: Unsupported Expressions — 64-bit ALU Operations (11 hits)

### 4a. `Mul64(...)` — 6 hits across 2/8 subjects

**Subjects:** json(3), mjs(3)

**Semantics:** 64-bit multiplication. Used for array index calculations (`size * index`), GC pointer arithmetic.

**What to change:**
- `VexSyntax.lean`: Add `| mul64 : Expr Reg -> Expr Reg -> Expr Reg`
- Eval: standard `UInt64` multiplication

**Difficulty:** Easy

### 4b. `Not64(...)` — 1 hit (mjs)

**Semantics:** 64-bit bitwise NOT. `mbuf_insert` uses it.

**What to change:** Add `| not64 : Expr Reg -> Expr Reg`

**Difficulty:** Easy

### 4c. `Sar64(...)` — 1 hit (mjs, `b64dec`)

**Semantics:** 64-bit arithmetic right shift.

**What to change:** Add `| sar64 : Expr Reg -> Expr Reg -> Expr Reg`

**Difficulty:** Easy-Medium (signed shift semantics)

### 4d. `MullU64(...)` — 1 hit (parson, `json_object_init`)

**Semantics:** Unsigned 64-bit full multiply (128-bit result, return high 64 bits). Used for fast division-by-constant optimization (multiply by magic constant then shift).

**What to change:** Add `| mullU64 : Expr Reg -> Expr Reg -> Expr Reg` returning high 64 bits. Or: model as opaque since the optimization pattern is typically folded into a constant result.

**Difficulty:** Medium (128-bit arithmetic in Lean, or abstract it)

---

## Category 5: Unsupported Conditions (8 hits)

### 5a. `CmpNE64(...)` — 3 hits across 2/8 subjects

**Subjects:** cjson(1), parson(2)

**Semantics:** 64-bit not-equal comparison. Logically `not (eq64 a b)`.

**What to change:** In `parseCond` or `parseExpr` (since it appears in expression context), add:
- If in condition context: `.ok (.not (.eq64 l r))` — but `Cond` has no `not` constructor. Could use `isCondOp` extension.
- Better: rewrite as expression returning 1/0 and handle in context.
- Simplest: Add `CmpNE64` to `isCondOp` list and add case in `parseCond`: negation of `eq64`.

Note: these actually appear in *expression* context (assigned to a tmp), not just guard context. The parser tries to parse them as expressions first. Need to handle them either by:
1. Making them conditions and tracking in condMap, or
2. Adding a conditional expression to `Expr` (e.g., `| ite : Cond Reg -> Expr Reg -> Expr Reg -> Expr Reg`)

**Difficulty:** Easy if adding to `parseCond`; Medium if they appear in expression-only contexts

### 5b. `CmpNE32(...)` — 1 hit (parson)

**Semantics:** 32-bit not-equal. Same approach as 5a but narrowed.

**Difficulty:** Easy

### 5c. `CmpLE64S(...)` — 2 hits across 2/8 subjects

**Subjects:** cjson(1), mjs(1)

**Semantics:** Signed 64-bit less-than-or-equal. Already have unsigned `CmpLE64U`. Signed variant needs bias trick (add `2^63` then unsigned compare), same pattern as existing `CmpLT32S`/`CmpLE32S`.

**What to change:** Add case in `parseCond`.

**Difficulty:** Easy (follow existing signed comparison pattern)

### 5d. `amd64g_calculate_condition` with non-standard codes — 3 hits across 2/8 subjects

**Subjects:** parson(1: code=0xe), mjs(2: code=0x8)

**Semantics:** VEX helper for x86 condition flag computation. Code 0x8 = "signed less than" (`conditionCode_S`), code 0xe = "always" or "signed LE" depending on VEX version. The parser already handles `amd64g_calculate_condition` as a *condition*, but these appear in *expression* context (assigned to a tmp used as a value, not a guard). The `parseExpr` path hits `unsupported expression` because `amd64g_calculate_condition` is only handled in `parseCond`/`handleTmpAssign`.

**What to change:** `handleTmpAssign` already routes `amd64g_calculate_condition` to `parseCond`. The issue is these show up in a context where the condition result is used as a *value* (0 or 1), not just as a branch guard. Need to track the condition in `condMap` AND emit a `wrTmp` with an expression that evaluates the condition to 0/1.

**Difficulty:** Medium

---

## Category 6: Missing Condition Tracking — `no condition tracked for tN` (16 hits)

**Subjects:** cjson(8), parson(1), mjs(7)

**Semantics:** The parser tracks conditions in a `condMap` (tmp -> Cond). When an `if (tN)` guard references a tmp that wasn't recorded as a condition, parsing fails. This happens when:
1. The condition was computed via an unsupported op (so it was never added to condMap)
2. The condition was computed in a way the parser doesn't recognize (e.g., result of a CCall, or complex boolean logic)

**What to change:** This is a *downstream* failure — fixing the unsupported operations above (especially CmpNE64, And32 used as boolean tests, amd64g_calculate_condition in expression context) will fix most of these.

For the remaining cases, a fallback could treat any non-zero tmp value as "true" by emitting a synthetic `CmpNE64(tN, 0)` condition when the direct lookup fails.

**Difficulty:** Easy (fallback) to Medium (proper fix requires fixing upstream ops first)

---

## Category 7: Miscellaneous Unsupported Expressions (5 hits)

### 7a. `ITE(...)` — 4 hits across 2/8 subjects

**Subjects:** parson(1), mjs(3)

**Semantics:** VEX IR conditional expression: `ITE(cond, true_val, false_val)`. A ternary operator at the IR level. Used for branchless conditional moves (cmov instructions).

**What to change:**
- `VexSyntax.lean`: Add `| ite : Cond Reg -> Expr Reg -> Expr Reg -> Expr Reg` or similar
- `VexIRParser.lean`: Parse `ITE(guard, then, else)` where guard is a tmp (looked up in condMap)
- Eval: `if cond then then_val else else_val`

**Difficulty:** Medium (needs Cond integration in Expr evaluation)

### 7b. `Or8(...)` / `And8(...)` — 3 hits (cjson only)

**Semantics:** 8-bit bitwise OR/AND. Used for flag bit manipulation on byte-width values.

**What to change:** Either add `or8`/`and8` constructors, or treat as 64-bit ops masked to 8 bits. Simplest: parse `Or8(a,b)` as `narrow8(or64(a,b))` (if narrow8 exists) or just `or64(a,b)` (since upper bits don't matter for byte stores).

**Difficulty:** Trivial-Easy

### 7c. `64UtoV128(...)` — 1 hit (mjs, `mjs_ffi_cb_free`)

**Semantics:** Zero-extend a 64-bit value to 128-bit SIMD vector. Used for FFI callback setup (putting a value into xmm register).

**What to change:** Would need SIMD vector type modeling. For now, treat as opaque/skip.

**Difficulty:** Hard (SIMD semantics); can be deferred

---

## Priority Implementation Order

By impact (functions unblocked):

| Priority | Fix | Hits | Subjects | Difficulty |
|----------|-----|------|----------|------------|
| **P0** | Add registers: fs, r8, rbx, r9, r11, r12 | 273 | 8/8 | Easy |
| **P1** | Add `1Uto8` passthrough | 26 | 3/8 | Trivial |
| **P2** | Add `64to8` (truncate to byte) | 34 | 6/8 | Trivial |
| **P3** | Add `And32` / `Or32` / `Xor32` | 25 | 4/8 | Easy |
| **P4** | Add xmm0/xmm0lq register (opaque FP) | 24 | 3/8 | Medium |
| **P5** | Add `CmpNE64` / `CmpNE32` / `CmpLE64S` conditions | 6 | 3/8 | Easy |
| **P6** | Add `Mul64` / `Mul32` | 7 | 3/8 | Easy |
| **P7** | Add `ITE` expression | 4 | 2/8 | Medium |
| **P8** | Add `8Sto64` (compose sext8to32 + sext32to64) | 3 | 2/8 | Trivial |
| **P9** | Add `Not32` / `Not64` / `Sar32` / `Sar64` | 4 | 2/8 | Easy-Medium |
| **P10** | Add `Or8` / `And8` | 3 | 1/8 | Trivial |
| **P11** | Add `MullU64` (128-bit multiply high) | 1 | 1/8 | Medium |
| **P12** | Add `amd64g_calculate_condition` in expr context | 3 | 2/8 | Medium |
| **P13** | Add ymm0 / 64UtoV128 (SIMD) | 2 | 1/8 | Hard |

**P0 alone recovers ~62% of failures.** P0+P1+P2+P3 recovers ~81%.

---

## Files That Need Changes

| File | Changes |
|------|---------|
| `Instances/ISAs/VexAmd64.lean` | Expand `Amd64Reg` enum, update all instances |
| `Instances/ISAs/VexIRParser.lean` | `resolveReg` (new registers), `parseExpr` (new ops), `parseCond` (new comparisons) |
| `Instances/ISAs/VexSyntax.lean` | New `Expr` constructors (mul64, and32, or32, xor32, narrow8, not32, not64, sar32, sar64, ite, mul32, sar64, mullU64) |
| `Instances/ISAs/VexCompTree.lean` | `evalExpr` cases for new constructors |
| Proof files referencing `Amd64Reg` exhaustive matches | Will need new cases |
