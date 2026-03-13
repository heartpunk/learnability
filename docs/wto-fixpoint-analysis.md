# WTO Fixpoint — Problem Analysis

## Goal
Replace the two-level stratified fixpoint (manual function ordering + per-function
convergence) with an automatic Bourdoncle WTO that discovers the iteration order.

## What Works in Current Code
- `WTOComponent` type, `wtoVisit`/`computeWTO` (Bourdoncle 1993 algorithm) — correct
- `processDAGBlock`, `processSCCStabilization`, `processWTOComponent` — correct logic
- `buildCFGSuccessors` with `funcBlockAddrs` for indirect jumps — works but insufficient
- `computeFunctionStabilization` — reused as convergence engine, unchanged and correct
- Grammar extraction — works independently of WTO (uses raw body branches)
- All dead code deleted: `computeStabilizationHS`, `computeStabilization`,
  `computeStabilizationNaive`, `buildDispatchBody`, `composeBranchArrayStratified`,
  `splitBodyAndExpandCalls`, old `stratifiedFixpoint`, `ChunkResult`/`composeChunk`/
  `splitIntoChunks`/`composeAndDedupParallel`

## The Problem: Incomplete Block-Level CFG

The WTO algorithm needs a complete CFG to detect cycles. `buildCFGSuccessors` constructs
edges from VEX body branches: for each branch, extract `rip-guard` (source block addr)
and `rip-target` (destination block addr). This produces an INCOMPLETE graph.

### Three categories of missing edges

**1. Indirect jumps (non-constant rip target)**
Block ends in `jmp rax` or `ret` (rip = load(mem, rsp)). `extractRipTarget` returns
`none`. The `funcBlockAddrs` fix adds fan-out to all sibling blocks, but this is an
overapproximation within one function and doesn't know the actual target.

**2. Call continuation blocks**
When function A's block X calls function B, the body branch has rip-target = B's entry.
But after B returns, execution continues at the block FOLLOWING X in A. This continuation
block has NO incoming edge from X in the CFG — the call/return linkage isn't represented.
The continuation is only reachable because B sets rip = return address (from stack).

**3. Blocks reachable only via cross-function branch targets**
Some blocks within function A are only reachable because a block in function B has a
conditional branch targeting them (e.g., fall-through after a call). No intra-function
path from A's entry reaches these blocks.

### Measured impact
- DFS from next_sym entry (0x40006f): reaches 31 of 55 blocks
- DFS from term entry (0x400427): reaches ~9 of 10 blocks
- DFS from ALL 7 function entries combined: only 56 of 150 blocks reachable
- The remaining 94 blocks are only reachable as DFS roots (separate trees)

### Why this breaks WTO cycle detection
The cross-function call edges DO exist in the CFG (e.g., 0x4004a6 → 0x40064d for
term→paren_expr). But block 0x4004a6 is NOT reachable from term's entry (0x400427)
via the extracted CFG. So DFS from term's entry never traverses that edge.

When we add all 150 block addresses as DFS roots (for coverage), individual blocks
get visited in their own small DFS trees BEFORE the function-entry DFS reaches them
via cross-function edges. This fragments the graph: by the time DFS from term tries
to follow the edge to paren_expr, paren_expr has already been assigned dfn=∞ (popped
as a trivial SCC in an earlier mini-tree). No back edge is detected.

Result: 0 inter-function SCCs detected. The mutual recursion cycle
statement→paren_expr→expr→test→sum→term→paren_expr is completely missed.
All 4 detected SCCs are small intra-function loops (within sum and statement).

### Verified incorrect output
Entry-block branch counts with current WTO vs old stratified (CORRECT):

| Function   | WTO entry-only | Old stratified |
|------------|---------------|----------------|
| next_sym   | 71            | 75             |
| term       | 74            | 40             |
| sum        | 74            | 29             |
| test       | 74            | 27             |
| expr       | 148           | 72             |
| paren_expr | 72            | 67             |
| statement  | 6             | 214            |

Every function mismatches. The WTO produces raw block-level compositions, not
function-level converged summaries. The all-blocks aggregation is even more wrong
(394, 366, 234, 223, 523, 587, 1583).

## Why the Old Stratified Architecture Works
`computeFunctionStabilization` operates on a FLAT array of all body branches for a
function. It doesn't need a block-level CFG at all — it just composes
body × frontier repeatedly until convergence. The manual function ordering
(next_sym first, then NT functions in rounds) handles inter-function dependencies.

## Two Fix Directions

### Option A: Complete the block-level CFG
Add call-return edges: when block X at address A calls function B (rip-target = B_entry),
add an edge from A to A+blocksize (the continuation/return block). This requires knowing
block sizes or using the VEX parser's address-to-next-address mapping.

Pros: Makes block-level WTO work as originally planned. Inner loops (while/for) would
nest inside outer mutual recursion. Each nesting level converges independently.

Cons: Need to reliably identify call-return pairs in VEX IR. The "next address" after
a call block might not be straightforward (VEX blocks vary in size). May need parser
changes. Also, `processDAGBlock` and `processSCCStabilization` operate at block
granularity — need to verify they produce correct function-level summaries.

Fundamental concern: even with a complete CFG, the block-level WTO approach produces
per-BLOCK summaries (what does block X do given all possible inputs?), not per-FUNCTION
summaries (what does the function do from entry to exit?). The old architecture produces
per-function summaries. These are conceptually different — the block-level approach
would need all blocks in a function to be in the same SCC (since blocks within a function
ARE mutually reachable via the call/return/continuation structure), which would just
degenerate to function-level convergence anyway.

### Option B: Function-level WTO
Build WTO over the 7 function nodes. Edges = cross-function calls extracted from body
branches (already reliably extracted — we see 41 cross-function edges in the current
output). DAG functions get single-pass `computeFunctionStabilization`. SCC function
groups get iterated `splitBodyAndExpandCalls` + `computeFunctionStabilization` until
convergence (exactly like old Phase 2, but with automatic ordering).

Pros: Simple. Reuses existing per-function convergence machinery verbatim. Only change
is replacing manual ordering with WTO-computed ordering. Guaranteed correct because
it's structurally equivalent to the old approach.

Cons: Doesn't provide inner-loop nesting benefits (while/for loops don't get their own
convergence level). Less ambitious than the original plan. But for this binary, the old
approach already converges in 3 rounds, so the benefit of nesting is theoretical.

## Current State of Code (as of 2026-03-13)
- `wtoFixpoint` exists but produces wrong results (block-level WTO)
- `stratifiedFixpoint` has been deleted
- `splitBodyAndExpandCalls` has been deleted (needed for Option B)
- `computeFunctionStabilization` is intact and correct
- Dead code cleanup is done (~460 lines removed)
- Old stratified output available via worktree at /tmp/old_dispatch/
- Diagnostic logging added: WTO structure, SCC details, coverage verification,
  old-vs-new comparison
