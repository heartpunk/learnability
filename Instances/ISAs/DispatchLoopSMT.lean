import Instances.ISAs.DispatchLoopEval

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## SMT Query Cache (Green-style)

Green (Visser et al. 2012) caches solver results by canonicalizing and hashing
the query formula.  On cache hit, the solver call is skipped entirely.

Pipeline: CANONIZE → HASH → CACHE LOOKUP → (miss?) CVC5 → STORE

The cache maps: hash(canonicalizePC(assertion)) → Bool (true = UNSAT).
Implication queries (A → B) are represented as (A ∧ ¬B): UNSAT means A implies B.
Equivalence queries (A ↔ B) are decomposed into two implication queries. -/

/-- SMT query cache: hash of canonicalized assertion formula → UNSAT result. -/
abbrev SMTCache := Std.HashMap UInt64 Bool

/-- Cache key for an implication query "does A imply B?",
    i.e. is (A ∧ ¬B) UNSAT?  Uses depth-limited hash directly rather than
    full canonicalization (which traverses the entire expression tree —
    89% of CPU for QuickJS per GDB sampling). More cache misses for
    semantically equivalent but syntactically different queries, but
    those are rare in practice and the cost is just a redundant CVC5 call. -/
def smtImplCacheKey {Reg : Type} [Hashable Reg] (a b : SymPC Reg) : UInt64 :=
  mixHash (hash a) (hash b)

/-- Run a batch of SMT implication queries with caching (backed by CVC5).
    Each query (A, B) checks: is (A ∧ ¬B) UNSAT? (i.e. does A → B?)
    Returns: (results array aligned with input, cache hits count).
    Updates the cache ref with new results. -/
def smtCheckImplCached {Reg : Type} [BEq Reg] [Hashable Reg] [ToString Reg]
    (cache : IO.Ref SMTCache)
    (pairs : Array (SymPC Reg × SymPC Reg))
    (tmpFile : System.FilePath := ".lake/smt_cached.smt2") :
    IO (Array Bool × Nat) := do
  if pairs.size == 0 then return (#[], 0)
  let t0 ← IO.monoMsNow
  let c ← cache.get
  -- Phase 1: check cache, collect misses.
  -- missOrigIdx[j] = index into `pairs`; missPairs[j] = the (A,B) pair.
  let mut results : Array (Option Bool) := Array.replicate pairs.size none
  let mut missOrigIdx : Array Nat := #[]
  let mut missPairs : Array (SymPC Reg × SymPC Reg) := #[]
  let mut hits : Nat := 0
  let mut pairIdx : Nat := 0
  for (a, b) in pairs do
    let key := smtImplCacheKey a b
    match c.get? key with
    | some v => results := results.set! pairIdx (some v); hits := hits + 1
    | none =>
      missOrigIdx := missOrigIdx.push pairIdx
      missPairs := missPairs.push (a, b)
    pairIdx := pairIdx + 1
  let t1 ← IO.monoMsNow
  if pairs.size > 10000 then
    IO.eprintln s!"      [smt-trace] cache check: {t1 - t0}ms, {pairs.size} pairs → {hits} hits, {missPairs.size} misses"
  -- Phase 2: batch CVC5 for cache misses (parallel across cores)
  if missPairs.size > 0 then
    let chunkSize := 1000
    let totalChunks := (missPairs.size + chunkSize - 1) / chunkSize
    if pairs.size > 10000 then
      IO.eprintln s!"      [smt-trace] starting script gen: {missPairs.size} misses in {totalChunks} chunks"
      (← IO.getStderr).flush
    -- Step 2a+2b: write scripts directly to files and run CVC5 in parallel batches.
    -- No in-memory script accumulation — avoids O(n²) string concat blowup.
    let t_gen_start ← IO.monoMsNow
    let maxParallel := min 8 totalChunks
    let mut allChunkResults : Array (Nat × Array Bool) := #[]
    let mut chunkStart := 0
    let mut chunkIdx := 0
    -- Process in parallel batches
    while chunkStart < missPairs.size do
      let batchEnd := min (chunkIdx + maxParallel) totalChunks
      let t_batch_start ← IO.monoMsNow
      -- Write chunk files and launch CVC5 for this batch
      let mut tasks : Array (Task (Except IO.Error (Nat × Array Bool))) := #[]
      while chunkIdx < batchEnd && chunkStart < missPairs.size do
        let chunkEnd := min (chunkStart + chunkSize) missPairs.size
        let chunk := missPairs.extract chunkStart chunkEnd
        let chunkFile := s!".lake/smt_chunk_{chunkIdx}.smt2"
        let ci := chunkIdx
        -- Collect register names for preamble
        let mut regNames : Std.HashSet String := {}
        let mut needsMem := false
        for (a, b) in chunk do
          regNames := SymPC.collectRegNames a regNames
          regNames := SymPC.collectRegNames b regNames
          if SymPC.hasLoad a || SymPC.hasLoad b then needsMem := true
        -- Write directly to file — no string accumulation
        let h ← IO.FS.Handle.mk chunkFile .write
        h.putStr (smtPreamble regNames needsMem)
        for (a, b) in chunk do
          h.putStr "(push)\n"
          h.putStr s!"(assert (and {SymPC.toSMTLib a} (not {SymPC.toSMTLib b})))\n"
          h.putStr "(check-sat)\n"
          h.putStr "(pop)\n"
        h.putStr "(exit)\n"
        h.flush
        -- Launch CVC5 asynchronously
        let task ← IO.asTask (prio := .default) do
          let out ← IO.Process.output { cmd := "cvc5", args := #["--incremental", chunkFile] }
          return (ci, parseSMTResults out.stdout)
        tasks := tasks.push task
        chunkStart := chunkEnd
        chunkIdx := chunkIdx + 1
      -- Wait for all tasks in this batch
      for task in tasks do
        match task.get with
        | .ok (ci, chunkRes) =>
          allChunkResults := allChunkResults.push (ci, chunkRes)
        | .error e => throw e
      let t_batch_end ← IO.monoMsNow
      if pairs.size > 10000 then
        IO.eprintln s!"      [smt-trace] batch: chunks up to {chunkIdx}/{totalChunks}, {t_batch_end - t_batch_start}ms ({maxParallel} parallel)"
    let t_gen_end ← IO.monoMsNow
    if pairs.size > 10000 then
      IO.eprintln s!"      [smt-trace] all chunks done in {t_gen_end - t_gen_start}ms"
    -- Merge results in chunk order
    let sortedResults := allChunkResults.qsort (fun a b => a.1 < b.1)
    let mut allMissResults : Array Bool := #[]
    for (_, chunkRes) in sortedResults do
      allMissResults := allMissResults ++ chunkRes
    -- Store results in cache and in output array
    let t_store_start ← IO.monoMsNow
    let mut c' ← cache.get
    let mut missIdx : Nat := 0
    for (a, b) in missPairs do
      let isUnsat := if h : missIdx < allMissResults.size then allMissResults[missIdx] else false
      if h2 : missIdx < missOrigIdx.size then
        results := results.set! missOrigIdx[missIdx] (some isUnsat)
      c' := c'.insert (smtImplCacheKey a b) isUnsat
      missIdx := missIdx + 1
    cache.set c'
    let t_store_end ← IO.monoMsNow
    if pairs.size > 10000 then
      IO.eprintln s!"      [smt-trace] store results: {t_store_end - t_store_start}ms, total smt: {t_store_end - t0}ms"
  -- Phase 3: unwrap
  return (results.map (fun r => r.getD false), hits)

