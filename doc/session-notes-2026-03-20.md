# Session Notes — 2026-03-18 through 2026-03-20

## Major Accomplishments

### WTO Fixpoint (Steps 0-3 of original plan)
- PathEvent/PathHistory types added
- Bourdoncle's WTO algorithm (computeWTO with fuel-based termination)
- wtoFixpoint replaces hardcoded 2-phase stratifiedFixpoint
- Wired as default pipeline, --legacy flag for old path
- Function dedup by entry address (removes .localalias)

### File Split (5 → 8 files)
- DispatchLoopEval.lean (Core, 815 lines)
- DispatchLoopSMT.lean (SMT cache + parallel CVC5, ~140 lines)
- DispatchLoopStabilization.lean (~1100 lines)
- DispatchLoopFunctionStab.lean (computeFunctionStabilization, ~640 lines)
- DispatchLoopWTO.lean (PathHistory + WTO types + orchestration, ~485 lines)
- DispatchLoopGrammar.lean (~1700 lines)
- DispatchLoopPipeline.lean (~500 lines)
- Pipeline rebuilds in ~10s, WTO in ~30s. Only FunctionStab has heavy codegen.

### VEX Parser Extensions
- CmpEQ16, CmpNE16, CmpNE8, CmpLT64S, Sub8
- 1-arg float conversion variants (I32StoF64 etc.)
- F0x2 SIMD naming aliases (Add64F0x2 etc.)
- r10, r13-r15 register mapping
- FP/SSE support merged from agent workspace (xmm registers, F64 types)

### Performance Fixes
- Constant folding in lowerExpr (fixes cgi_decode init_hex_values)
- HashMap SymTempEnv (was O(n) closure chain, now O(1))
- Array-based flatBodyDenotArray (avoids Finset DecidableEq)
- Hash-cached dedup (currentByHash parallel HashMap)
- Depth-limited hash for SymExpr/SymMem (cap at 4 levels)
- **Cached canonicalized closure PCs** — eliminated 89% of CPU (424K redundant
  canonicalizePC calls → 268 calls). Found via GDB stack sampling.
- **Parallel CVC5** — 8 concurrent solver instances via IO.asTask. ~6x speedup.
- **Write-through SMT scripts** — write directly to file handles instead of
  O(n²) string concatenation. Eliminated 55GB OOM (now ~4GB RSS).
- **Depth-limited smtImplCacheKey** — replaced canonicalizePC with mixHash
  in SMT cache key computation.

### New Subjects (13 total)
- Original 9 parsers: tinyc, json, calc, lisp, cgi_decode, simplearithmeticparser, cjson, parson, mjs
- Terminal emulators: libtsm (converges, 2111 branches), st (converges)
- Bytecode interpreters: Lua luaV_execute (converges K=3, 2329 branches, ~2min),
  QuickJS JS_CallInternal (1688 branches, K=0 in progress — first time ever getting this far)

### Generic Dispatch Table + LTS
- extractComparisons: walks SymPC for eq(expr, const) pairs
- extractDispatchTable: groups branches by DispatchKey (comparison tuple)
- constructLTS: GenericExtractedLTS with DispatchKey labels + SymSub effects
- Grammar interpretation layer: findProducers → classify by direct-lexer-caller →
  ParserStructure → printLTSGrammar. tinyc at 13/19 golden match.
- Structural golden comparison V2 (name-independent bipartite matching)
- Golden grammar loading from stalagmite JSON files

### Infrastructure
- Parallel analysis runner (just analyze-all-parallel) with timestamped run dirs
- stdout buffering fix (flush after each log line + stdbuf)
- Durable trace logging (compose/simplify/dedup/SMT per-phase timing)
- GDB stack sampling script (/tmp/gdb_sample.sh)

## QuickJS Status (as of end of session)
- 1688 body branches, 12 projected registers, 268 closure PCs
- Compose: 1ms, Simplify: ~50s, Dedup: ~195s (depth-limited hash: was 602s)
- Syntactic sigs + syn matching + cache check: <1s (was 30+ min before closure caching)
- SMT: 126,496 queries in 127 chunks, writing to files (not accumulating strings)
- RSS: ~4GB (was 55GB OOM before write-through fix)
- Currently in script writing/CVC5 phase — first time ever reaching this point
- Unknown whether K=0 will complete or if CVC5 will be too slow on the large formulas

## Design Docs
- doc/principled-detection-design.md — Generic dispatch table core + 7 domain layers
- doc/opsem-extraction-notes.md — Opsem validation on tinyc run/c
- doc/opsem-validation-tinyc-run.md — Detailed opcode dispatch analysis
- doc/new-subjects-status.md — Terminal emulator + interpreter status

## Key Architectural Decisions
- Generic LTS must be produced as intermediate representation (cslib compatible)
- Domain layers (grammar/state-machine/opsem) read LTS, don't access raw branches
- No heuristics in core — domain-specific heuristics in interpretation layers only
- Dispatch table groups branches by FULL comparison tuple (supports multi-level dispatch)
- Co-refinement projection (closedRegs) IS the formal fixpoint — domain layers interpret it

## Workspaces
- learnability-fp-coverage: merged, workspace deleted
- learnability-golden-comparison: merged, workspace deleted
- learnability-terminal-subjects: merged, workspace deleted

## Latest QuickJS Run (writeToSMTLib fix)
- Simplify: 34s, Dedup: 174s, Syn matching: 10s (1112 matched, 471 need SMT)
- Entered smtCheckImplCached with 126K pairs at 13GB RSS
- CVC5 phase in progress — first time with writeToSMTLib (no string building)
- Previous run OOMed at 55GB during string concat in toSMTLib
- Check .lake/runs/quickjs-writethrough/quickjs.log for results

## Performance Fix Chain (QuickJS K=0 path)
1. Depth-limited hash: dedup 602s → 195s
2. Closure PC caching: canonicalize 30min → 12ms (GDB found canonicalizeExpr 89% CPU)
3. smtImplCacheKey: replaced canonicalizePC with mixHash
4. Write-through SMT: eliminated O(n²) string concat at chunk level
5. writeToSMTLib: eliminated O(n²) string concat at per-query level (GDB found toSMTLib 89% CPU)
6. Parallel CVC5: 8 concurrent instances via IO.asTask

## What's Next (from plan)
1. Fix grammar extraction terminal resolution (currently 13/19, should be ~20/20)
2. Implement state machine interpretation layer (libtsm, st)
3. Implement opsem interpretation layer (tinyc run, Lua, QuickJS)
4. Wait for QuickJS K=0 to complete and see if it converges
5. Hash-consing (CExpr wrapper) for permanent dedup fix
6. Consider whether QuickJS needs further perf work or just more patience
