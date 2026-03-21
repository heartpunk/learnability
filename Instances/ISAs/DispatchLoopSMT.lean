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

/-- SMT query cache: hash → bucket of ((a, b), result) entries.
    Uses hash as fast-path, verifies structural equality on hit for soundness. -/
abbrev SMTCache (Reg : Type) := Std.HashMap UInt64 (Array (SymPC Reg × SymPC Reg × Bool))

/-- Cache key for an implication query "does A imply B?",
    i.e. is (A ∧ ¬B) UNSAT?  Uses depth-limited hash directly rather than
    full canonicalization (which traverses the entire expression tree —
    89% of CPU for QuickJS per GDB sampling). -/
def smtImplCacheKey {Reg : Type} [Hashable Reg] (a b : SymPC Reg) : UInt64 :=
  mixHash (hash a) (hash b)

/-- Run a batch of SMT implication queries with caching (backed by CVC5).
    Each query (A, B) checks: is (A ∧ ¬B) UNSAT? (i.e. does A → B?)
    Returns: (results array aligned with input, cache hits count).
    Updates the cache ref with new results. -/
def smtCheckImplCached {Reg : Type} [BEq Reg] [DecidableEq Reg] [Hashable Reg] [ToString Reg]
    (cache : IO.Ref (SMTCache Reg))
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
    let mut found := false
    match c.get? key with
    | some bucket =>
      for hi : i in [:bucket.size] do
        let (ca, cb, cv) := bucket[i]
        if ca = a && cb = b then
          results := results.set! pairIdx (some cv)
          hits := hits + 1
          found := true
    | none => pure ()
    if !found then
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
        -- Collect unique PCs and build query plan to avoid writing the same
        -- PC hundreds of times.  In a 472×268 grid, each chunk has ~4 unique
        -- "a" PCs and ~268 unique "b" PCs — define-fun once, reference by name.
        -- Use hash-based lookup to avoid O(n²) DecidableEq on huge trees.
        let mut uniqueAs : Array (SymPC Reg) := #[]
        let mut uniqueBs : Array (SymPC Reg) := #[]
        -- Hash → array of indices into uniqueAs/uniqueBs that share that hash.
        -- On lookup: check hash first (O(1)), then equality only within bucket.
        let mut hashToA : Std.HashMap UInt64 (Array Nat) := {}
        let mut hashToB : Std.HashMap UInt64 (Array Nat) := {}
        let mut queryPlan : Array (Nat × Nat) := #[]
        for (a, b) in chunk do
          let ha := hash a
          let mut ai := uniqueAs.size
          match hashToA.get? ha with
            | some bucket =>
              let mut found := false
              for hk : k in [:bucket.size] do
                let idx := bucket[k]
                if h : idx < uniqueAs.size then
                  if uniqueAs[idx] = a then
                    ai := idx
                    found := true
              if !found then
                hashToA := hashToA.insert ha (bucket.push ai)
                uniqueAs := uniqueAs.push a
            | none =>
              hashToA := hashToA.insert ha #[ai]
              uniqueAs := uniqueAs.push a
          let hb := hash b
          let mut bi := uniqueBs.size
          match hashToB.get? hb with
            | some bucket =>
              let mut found := false
              for hk : k in [:bucket.size] do
                let idx := bucket[k]
                if h : idx < uniqueBs.size then
                  if uniqueBs[idx] = b then
                    bi := idx
                    found := true
              if !found then
                hashToB := hashToB.insert hb (bucket.push bi)
                uniqueBs := uniqueBs.push b
            | none =>
              hashToB := hashToB.insert hb #[bi]
              uniqueBs := uniqueBs.push b
          queryPlan := queryPlan.push (ai, bi)
        -- Emit define-funs for unique PCs
        for ha : i in [:uniqueAs.size] do
          h.putStr s!"(define-fun _a{i} () Bool "
          SymPC.writeToSMTLib h uniqueAs[i]
          h.putStr ")\n"
        for hb : i in [:uniqueBs.size] do
          h.putStr s!"(define-fun _b{i} () Bool "
          SymPC.writeToSMTLib h uniqueBs[i]
          h.putStr ")\n"
        -- Emit queries referencing define-fun names
        for (ai, bi) in queryPlan do
          h.putStr s!"(push)\n(assert (and _a{ai} (not _b{bi})))\n(check-sat)\n(pop)\n"
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
      let ck := smtImplCacheKey a b
      let bucket := c'.getD ck #[]
      c' := c'.insert ck (bucket.push (a, b, isUnsat))
      missIdx := missIdx + 1
    cache.set c'
    let t_store_end ← IO.monoMsNow
    if pairs.size > 10000 then
      IO.eprintln s!"      [smt-trace] store results: {t_store_end - t_store_start}ms, total smt: {t_store_end - t0}ms"
  -- Phase 3: unwrap
  return (results.map (fun r => r.getD false), hits)

