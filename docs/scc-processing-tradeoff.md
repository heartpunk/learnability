# Inter-Function SCC Processing: Block-Level vs Function-Level

## The Problem

The unified WTO correctly detects inter-function SCCs (e.g., the mutual recursion cycle
`statement → paren_expr → expr → test → sum → term → paren_expr`). With return edges
added to the CFG, Bourdoncle's algorithm finds the right cycle structure. However,
**block-level composition cannot follow return paths**.

### Why Block-Level Composition Fails for Inter-Function SCCs

Consider the call chain: block X (in `term`) calls `paren_expr` at address 0x40064d.
After `paren_expr` runs, it returns to X's continuation (the block after X in `term`).

At the block level:
1. **Call edges work**: Block X has `rip = const(0x40064d)`, so composition follows the
   edge into `paren_expr`'s entry block. ✓
2. **Return edges fail**: `paren_expr`'s return block has `rip = load(mem, rbp+0x8)` —
   a **non-constant** rip target. `extractRipTarget` returns `none`, and composition
   treats it as an exit branch. ✗

The CFG has the correct return edge (we added it in `buildReturnEdges`), but the
**symbolic composition** cannot follow it because:
- The return address is stored in memory (`rbp+0x8`) at call time
- To resolve it, composition would need to track the store chain across the entire
  callee's execution
- Load-after-store simplification works for single-block compositions, but across an
  entire function (multiple blocks, multiple paths), the symbolic memory grows too complex
  to match syntactically

### Measured Impact

With all CFG fixes (return edges + call-continuation edges), the WTO correctly finds:
- 6 return blocks, 67 call sites, 18 ret-edges, 49 call-continuation edges
- Inter-function SCC with 13 call-path blocks, expanded to 46 blocks via function membership
- But the SCC **converges at K=0** — the composition produces no new branches because
  it can never follow a return path

Output comparison (WTO vs old stratified, which is CORRECT):

| Function   | WTO entry-only | Old stratified |
|------------|---------------|----------------|
| next_sym   | varies        | 75             |
| term       | varies        | 40             |
| sum        | varies        | 29             |
| test       | varies        | 27             |
| expr       | varies        | 72             |
| paren_expr | varies        | 67             |
| statement  | varies        | 214            |

Every function mismatches.

## Why the Old Stratified Architecture Works

The old stratified approach operates at the **function level**:

1. **`splitBodyAndExpandCalls`**: For each function, separates body branches into:
   - **Non-call branches**: branches whose rip target is within the same function
   - **Call branches**: branches whose rip target is another function's entry.
     These are **replaced** by composing the call branch with the callee's current
     summary. This abstracts away the call/return mechanism entirely — instead of
     modeling `call → callee body → return`, it models `call → callee summary`.

2. **`computeFunctionStabilization`**: Takes the non-call body and the call-expanded
   branches as initial frontier, runs the standard convergence loop (compose, simplify,
   check PC-signature equivalence). This produces a function-level summary: "what does
   this function do from entry to exit?"

3. **Outer iteration**: Repeats over all mutually recursive functions until all summaries
   converge. Each outer round uses updated callee summaries.

The key insight: by replacing call branches with callee summaries, the approach never
needs to resolve return addresses. The symbolic return (`load(mem, rbp+0x8)`) is replaced
by the callee's actual effect on registers/memory.

## The Tradeoff

### Option A: Pure Block-Level (REJECTED)

Make block-level composition work by resolving return addresses symbolically.

**Why this is infeasible**:
- Would require tracking symbolic memory state across multi-block, multi-path callee
  execution
- The memory expression grows exponentially with nesting depth (each call adds a store
  chain, each return adds a load-after-store resolution attempt)
- Even with perfect load-after-store simplification, the symbolic state for a function
  with N blocks and multiple paths would require an exponential number of memory
  configurations
- This is equivalent to full symbolic execution — the entire point of compositional
  analysis is to avoid this

### Option B: Hybrid — Block-Level DAG + Function-Level SCC (CHOSEN)

Use block-level WTO for structure detection and DAG processing; switch to function-level
processing for inter-function SCCs.

**Design**:
1. WTO detects SCCs automatically (no manual function ordering)
2. DAG blocks get single-pass `processDAGBlock` (block-level composition) ✓
3. Intra-function SCCs (while/for loops) get `processSCCStabilization` (block-level) ✓
4. Inter-function SCCs get `processInterFuncSCC` (function-level):
   - Identify which functions participate in the SCC
   - For each function: split body into non-call + call-expanded (composing call branches
     with callee's current summary from cache)
   - Run `computeFunctionStabilization` per function
   - Repeat outer rounds until all function summaries converge
   - Update per-block cache from converged function summaries

**Why this is correct**:
- Structurally equivalent to the old stratified Phase 2
- Same convergence engine (`computeFunctionStabilization`)
- Same call-expansion mechanism (compose call branch with callee summary)
- Only difference: WTO-computed ordering instead of manual ordering

**What we lose vs pure block-level**:
- Inner loops within mutually recursive functions don't get their own convergence level
  (they're part of the function-level convergence). But for this binary, the old approach
  converges in 3 rounds, so the benefit is theoretical.

**What we gain**:
- Automatic function ordering (no manual stratification)
- Correct inter-function recursion handling
- Reuse of proven convergence machinery

## Detecting Inter-Function vs Intra-Function SCCs

An SCC is "inter-function" if its blocks belong to more than one function. We detect this
using `blockToFunc`: map each SCC block to its function entry, check if >1 distinct
function entries appear.

For intra-function SCCs (all blocks from one function, e.g., a while loop), block-level
`processSCCStabilization` works correctly because there are no call/return boundaries
to cross.

## Final Implementation (Verified Correct)

The actual implementation goes further than Option B: ALL functions use function-level
processing (not just inter-function SCCs). This is because block-level SCC processing
computes different closures than function-level, producing different convergence behavior.

### Architecture

1. **Block-level CFG analysis** (retained for diagnostics):
   - Parse VEX blocks, extract branches, build blocksByAddr
   - Build unified CFG with return edges (call/ret interprocedural linkage)
   - Compute block-level WTO (for SCC visualization and debugging)

2. **Function-level call graph** (new, for processing):
   - Build from blocksByAddr/blockToFunc: which functions call which
   - Compute function-level WTO via Bourdoncle's algorithm
   - Result: DAG functions (leaves) + SCC functions (mutual recursion)

3. **`splitBodyAndExpandCalls`**:
   - Splits function body into non-call branches + call-expanded branches
   - Call branches: rip target IS a function entry AND summary available
   - **Including self-recursive calls** when summary exists from previous outer round
   - Non-call: intra-function jumps, or calls without available summaries

4. **`processInterFuncSCC`** (used for ALL functions, not just SCCs):
   - Outer loop: iterate over functions in WTO order
   - Per function: splitBodyAndExpandCalls + computeFunctionStabilization
   - Convergence check: funcSummaries (separate from per-block cache)
   - On convergence: write full function summary to cache at entry address

### Key Insight: Self-Recursive Call Expansion

Self-recursive calls (e.g., `expr → expr`, `statement → statement`) must be expanded
using the current summary from the previous outer round. Without this, the summary
only captures non-recursive paths. With expansion, recursive structure propagates:

- Round 0: no self-summary → self-call stays as exit → partial summary
- Round 1: self-summary from round 0 → self-call expanded → fuller summary
- Round 2: converged (summary unchanged)

This matches the old stratified behavior exactly.

### Verified Results

All 7 functions match old stratified output:

| Function   | New WTO | Old Stratified | Match |
|------------|---------|----------------|-------|
| next_sym   | 75      | 75             | YES   |
| term       | 40      | 40             | YES   |
| sum        | 29      | 29             | YES   |
| test       | 27      | 27             | YES   |
| expr       | 72      | 72             | YES   |
| paren_expr | 67      | 67             | YES   |
| statement  | 214     | 214            | YES   |

Convergence structure:
- Function WTO: 2 DAG + 1 SCC component
- next_sym (leaf): converges in 1 outer round
- {term, sum, test, expr, paren_expr} (mutual recursion SCC): 2 outer rounds
- statement (depends on SCC): 2 outer rounds (self-recursion)
- Grammar extraction: all [OK], all 7 statement productions match golden
