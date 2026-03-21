import Instances.ISAs.DispatchLoopStabilization

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-- Per-function stabilization with optional initial frontier seeding.
    When initialFrontier is non-empty, those branches are added to the
    initial state (along with skip) instead of starting from skip alone.
    This is used to seed call-expanded results into the frontier without
    putting them in the body (which would cause expression nesting). -/
def computeFunctionStabilization {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg] [ToString Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))))
    (maxIter : Nat) (log : String → IO Unit)
    (smtCache : IO.Ref (SMTCache Reg))
    (initialFrontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[])
    (addrClassify : Option (AddrClassifier Reg) := none)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false) :
    IO (Option (Nat × Array (Branch (SymSub Reg) (SymPC Reg)))) := do
  let isa := vexSummaryISA Reg
  let initBranch := Branch.skip isa
  let (rawClosure, ripCount, dataCount) := extractClosure ip_reg bodyArr (dataOnly := true)
  -- Simplify closure PCs with same region classifier used for lifted PCs,
  -- so both sides of the closedness comparison are in the same normal form.
  let closure := match addrClassify with
    | some clf => rawClosure.map (simplifyLoadStorePCR clf)
    | none => rawClosure
  let mut current : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {}
  let mut currentByHash : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))) := {}
  current := current.insert initBranch
  currentByHash := currentByHash.insert (hash initBranch) #[initBranch]
  -- initialFrontier seeded into current AFTER closedness check (needs projection)
  -- Compute closed projection (same as computeStabilizationHS)
  let mut dataPCRegs : Std.HashSet Reg := {}
  let mut dataPCsHaveLoads := false
  for pc in closure do
    dataPCRegs := SymPC.collectRegsHS pc dataPCRegs
    if SymPC.hasLoad pc then dataPCsHaveLoads := true
  let mut closedRegs := dataPCRegs
  let mut closedNeedsMem := dataPCsHaveLoads
  let mut changed := true
  let mut closureRounds : Nat := 0
  while changed do
    changed := false
    closureRounds := closureRounds + 1
    for b in bodyArr do
      let currentRegsArr := closedRegs.toArray
      for r in currentRegsArr do
        let exprRegs := SymExpr.collectRegsHS (b.sub.regs r) {}
        for er in exprRegs do
          unless closedRegs.contains er || er == ip_reg do
            closedRegs := closedRegs.insert er
            changed := true
      if closedNeedsMem then
        let memRegs := SymMem.collectRegsHS b.sub.mem {}
        for mr in memRegs do
          unless closedRegs.contains mr || mr == ip_reg do
            closedRegs := closedRegs.insert mr
            changed := true
      unless closedNeedsMem do
        for r in currentRegsArr do
          if SymExpr.hasLoad (b.sub.regs r) then
            closedNeedsMem := true
            changed := true
  let closedRegsArr := closedRegs.toArray
  log s!"    closure: rip={ripCount} data={dataCount} proj=[{", ".intercalate (closedRegsArr.toList.map toString)}] ({closedRegsArr.size} regs, rounds={closureRounds})"
  let projHashOf (sub : SymSub Reg) : UInt64 := Id.run do
    let mut h : UInt64 := 0
    for r in closedRegsArr do
      h := mixHash h (hash (sub.regs r))
    if closedNeedsMem then h := mixHash h (hash sub.mem)
    return h
  -- Convergence via PC signature: syntactic fast-path + SMT semantic check.
  -- convRep{PCs,SynSigs,SemSigs}: one entry per discovered equivalence class.
  -- SynSig = which closure PCs the branch syntactically implies (List Bool).
  -- SemSig = which closure PCs the branch semantically implies (Array Bool);
  --          computed lazily via CVC5 the first time a syntactic mismatch occurs.
  -- Pre-canonicalize closure PCs once — avoids re-canonicalizing 268 PCs
  -- per branch (was 89% of CPU for QuickJS with 1583 branches × 268 closure).
  let closureCanon := closure.map canonicalizePC
  let mut convRepPCs     : Array (SymPC Reg)          := #[initBranch.pc]
  let mut convRepSynSigs : Array (List Bool)           := #[computePCSignature closure initBranch.pc closureCanon]
  let mut convRepSemSigs : Array (Option (Array Bool)) := #[none]
  -- Build initial frontier: skip + structurally-unique simplified seeds.
  let mut subPool : SubPool Reg := {}
  let mut frontierSet : Std.HashSet (Branch (SymSub Reg) (SymPC Reg)) := {initBranch}
  let mut frontier : Array (Branch (SymSub Reg) (SymPC Reg)) := #[initBranch]
  for b in initialFrontier do
    match simplifyBranchFull b addrClassify with
    | none => pure ()
    | some sb =>
      let zb := zeroNonProjected closedRegs ip_reg sb
      let (internedSub, subPool') := subPool.intern zb.sub
      subPool := subPool'
      let zb' : Branch (SymSub Reg) (SymPC Reg) := ⟨internedSub, zb.pc⟩
      unless frontierSet.contains zb' do
        frontierSet := frontierSet.insert zb'
        convRepPCs     := convRepPCs.push zb'.pc
        convRepSynSigs := convRepSynSigs.push (computePCSignature closure zb'.pc closureCanon)
        convRepSemSigs := convRepSemSigs.push none
        frontier := frontier.push zb'
  -- Seed initial frontier into current set
  for b in frontier do
    current := current.insert b
    let h := hash b
    currentByHash := currentByHash.insert h ((currentByHash.getD h #[]).push b)
  log s!"    initial frontier: {frontier.size} branches (skip + {initialFrontier.size} call-expanded)"
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    -- Pure composition: no summary interception, body has no call branches
    let t_compose ← IO.monoMsNow
    let (composedTagged, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr frontier
    let t_composed ← IO.monoMsNow
    -- Strip body indices (not used in this function)
    let composed := composedTagged.map (·.1)
    log s!"      [trace] compose: {t_composed - t_compose}ms, {composed.size} raw branches"
    -- Simplify: load-after-store + constant folding + zero non-projected
    let t_simplify ← IO.monoMsNow
    let mut simplified : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut droppedSimplify : Nat := 0
    for b in composed do
      match simplifyBranchFull b addrClassify with
      | none => droppedSimplify := droppedSimplify + 1
      | some sb =>
        let zb := zeroNonProjected closedRegs ip_reg sb
        let (internedSub, subPool') := subPool.intern zb.sub
        subPool := subPool'
        simplified := simplified.push ⟨internedSub, zb.pc⟩
    let t_simplified ← IO.monoMsNow
    log s!"      [trace] simplify: {t_simplified - t_simplify}ms, {simplified.size} survived, {droppedSimplify} dropped"
    let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut dupes : Nat := 0
    -- Phase 1: structural dedup — collect all branches not already in current
    -- Hash each branch ONCE upfront, then use cached hash for set operations
    let t_dedup ← IO.monoMsNow
    let mut semCands : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for b in simplified do
      let h := hash b
      let bucket := currentByHash.getD h #[]
      if bucket.any (· == b) then
        dupes := dupes + 1
      else
        currentByHash := currentByHash.insert h (bucket.push b)
        current := current.insert b
        semCands := semCands.push b
    let t_deduped ← IO.monoMsNow
    log s!"      [trace] dedup: {t_deduped - t_dedup}ms, {dupes} dupes, {semCands.size} new candidates"
    -- Branch cap: OOM safety valve
    if current.size > maxBranches then
      log s!"    BRANCH CAP: {current.size} > {maxBranches}, stopping early at K={k}"
      return some (k, current.toArray)
    -- Phase 2: PC-signature convergence (syntactic fast-path + SMT semantic).
    -- For each candidate, compute its signature: which closure PCs does it imply?
    -- Fast path: syntactic sig matches an existing rep sig → collapse.
    -- Slow path (CVC5): for candidates with new syntactic sigs, compute semantic sig
    --   (for each closure PC phi_i, is branch.pc AND NOT phi_i UNSAT?) and
    --   compare against rep semantic sigs.
    let mut semCollapsed : Nat := 0
    let t_smt_start ← IO.monoMsNow
    if semCands.size > 0 then
      -- Compute syntactic sigs for all candidates
      let t_synsig ← IO.monoMsNow
      let candSynSigs := semCands.map (fun c => computePCSignature closure c.pc closureCanon)
      let t_synsig_done ← IO.monoMsNow
      log s!"      [trace] syntactic sigs: {t_synsig_done - t_synsig}ms for {semCands.size} candidates × {closure.size} closure"
      -- Fast path: which candidates have a syntactic sig matching an existing rep?
      let t_synmatch ← IO.monoMsNow
      let mut synMatched : Std.HashSet Nat := {}
      for ci in [:semCands.size] do
        let csig := candSynSigs[ci]!
        let mut ri := 0
        while ri < convRepSynSigs.size do
          if convRepSynSigs[ri]! == csig then
            synMatched := synMatched.insert ci
            ri := convRepSynSigs.size  -- break
          ri := ri + 1
      let t_synmatched ← IO.monoMsNow
      -- Collect SMT candidates: those with no syntactic match
      let mut smtCandIdxs : Array Nat := #[]
      for ci in [:semCands.size] do
        unless synMatched.contains ci do
          smtCandIdxs := smtCandIdxs.push ci
      log s!"      [trace] syn matching: {t_synmatched - t_synmatch}ms, {synMatched.size} matched, {smtCandIdxs.size} need SMT (reps={convRepSynSigs.size})"
      -- Semantic path: only if there are unmatched candidates and closure is non-empty
      let mut candSemSigsArr : Array (Option (Array Bool)) := Array.replicate semCands.size none
      let mut totalSMTQueries := 0
      let mut totalSMTCacheHits := 0
      let mut semMatched : Std.HashSet Nat := {}
      if smtCandIdxs.size > 0 && closure.size > 0 then
        let n := closure.size
        -- Build batch of PCs needing semantic sig computation:
        let t_batch_build ← IO.monoMsNow
        let mut batchPCs      : Array (SymPC Reg) := #[]
        let mut batchIsRep    : Array Bool        := #[]
        let mut batchRepIdxs  : Array Nat         := #[]
        let mut batchCandIdxs : Array Nat         := #[]
        for ri in [:convRepPCs.size] do
          match convRepSemSigs[ri]? with
          | some none =>
            for pc in convRepPCs.extract ri (ri + 1) do
              batchPCs := batchPCs.push pc
            batchIsRep    := batchIsRep.push true
            batchRepIdxs  := batchRepIdxs.push ri
            batchCandIdxs := batchCandIdxs.push 0
          | _ => pure ()
        for ci in smtCandIdxs do
          for b in semCands.extract ci (ci + 1) do
            batchPCs := batchPCs.push b.pc
          batchIsRep    := batchIsRep.push false
          batchRepIdxs  := batchRepIdxs.push 0
          batchCandIdxs := batchCandIdxs.push ci
        let t_batch_built ← IO.monoMsNow
        log s!"      [trace] batch build: {t_batch_built - t_batch_build}ms, {batchPCs.size} PCs × {n} closure = {batchPCs.size * n} pairs"
        -- Batch CVC5 with caching: for each pc in batchPCs, n queries (one per closure PC).
        let t_pairs_start ← IO.monoMsNow
        let mut convPairs : Array (SymPC Reg × SymPC Reg) := #[]
        for pc in batchPCs do
          for phi in closure do
            convPairs := convPairs.push (pc, phi)
        let t_pairs_end ← IO.monoMsNow
        log s!"      [trace] convPairs array: {t_pairs_end - t_pairs_start}ms for {convPairs.size} pairs"
        let t_smt_call ← IO.monoMsNow
        log s!"      [trace] entering smtCheckImplCached: {convPairs.size} pairs"
        let (allSemResults, convHits) ← smtCheckImplCached smtCache convPairs ".lake/smt_semsig.smt2"
        let t_smt_done ← IO.monoMsNow
        log s!"      [trace] smtCheckImplCached done: {t_smt_done - t_smt_call}ms, {convHits} hits"
        totalSMTQueries := convPairs.size
        totalSMTCacheHits := convHits
        -- Assign sem sigs: allSemResults[si*n .. (si+1)*n] for batchPCs[si]
        let mut updatedRepSemSigs := convRepSemSigs
        let mut si := 0
        for isRep in batchIsRep do
          let semSig := allSemResults.extract (si * n) ((si + 1) * n)
          if isRep then
            let ri := batchRepIdxs[si]!
            updatedRepSemSigs := updatedRepSemSigs.set! ri (some semSig)
          else
            let ci := batchCandIdxs[si]!
            candSemSigsArr := candSemSigsArr.set! ci (some semSig)
          si := si + 1
        convRepSemSigs := updatedRepSemSigs
        -- Compare each SMT cand's semantic sig against all rep semantic sigs
        for ci in smtCandIdxs do
          if let some candSem := candSemSigsArr[ci]! then
            let mut ri := 0
            let mut matched := false
            while !matched && ri < convRepSemSigs.size do
              if let some repSem := convRepSemSigs[ri]! then
                if candSem == repSem then
                  semMatched := semMatched.insert ci
                  matched := true
              ri := ri + 1
      let t_smt_end ← IO.monoMsNow
      log s!"    smt conv: {totalSMTQueries}q (hits={totalSMTCacheHits} misses={totalSMTQueries - totalSMTCacheHits}) → syn-collapsed={synMatched.size} sem-collapsed={semMatched.size}"
      log s!"      [trace] smt phase: {t_smt_end - t_smt_start}ms ({totalSMTQueries} queries, {semCands.size} candidates, {closure.size} closure PCs)"
      -- Classify: collapse or promote to new equivalence class
      for ci in [:semCands.size] do
        if synMatched.contains ci || semMatched.contains ci then
          semCollapsed := semCollapsed + 1
        else
          for b in semCands.extract ci (ci + 1) do
            convRepPCs     := convRepPCs.push b.pc
            convRepSynSigs := convRepSynSigs.push candSynSigs[ci]!
            convRepSemSigs := convRepSemSigs.push candSemSigsArr[ci]!
            newBranches    := newBranches.push b
    let t_end ← IO.monoMsNow
    log s!"    K={k}: |S|={current.size} |new|={newBranches.size} |conv_reps|={convRepSynSigs.size} pairs={pairsComposed} skipped={skipped} dropped={dropped}+{droppedSimplify} dupes={dupes} sem_collapsed={semCollapsed} {t_end - t_start}ms"
    -- Diagnostic: dump expression details for first few iterations
    if k ≤ 4 && newBranches.size > 0 then
      -- Aggregate stats across all new branches
      let mut totalNodes : Nat := 0
      let mut totalUnresolved : Nat := 0
      let mut maxNodes : Nat := 0
      for b in newBranches do
        let mut bNodes : Nat := 0
        let mut bUnresolved : Nat := 0
        for r in closedRegsArr do
          let e := b.sub.regs r
          bNodes := bNodes + exprNodeCount e
          bUnresolved := bUnresolved + exprUnresolvedLoads e
        bNodes := bNodes + memNodeCount b.sub.mem
        totalNodes := totalNodes + bNodes
        totalUnresolved := totalUnresolved + bUnresolved
        if bNodes > maxNodes then maxNodes := bNodes
      log s!"      expr stats: total_nodes={totalNodes} avg={totalNodes / newBranches.size} max={maxNodes} unresolved_loads={totalUnresolved}"
      -- Dump first 2 new branches in detail
      let mut dumpIdx : Nat := 0
      for b in newBranches do
        if dumpIdx < 2 then
          let mut regSummaries : List String := []
          for r in closedRegsArr do
            let e := b.sub.regs r
            regSummaries := regSummaries ++ [s!"{r}={exprSummary e 3}[{exprNodeCount e}n,{exprUnresolvedLoads e}ul]"]
          log s!"      branch[{dumpIdx}]: {", ".intercalate regSummaries} mem[{memNodeCount b.sub.mem}n]"
          dumpIdx := dumpIdx + 1
    if newBranches.size == 0 then
      -- Collect all branches as array for the summary
      let summaryArr := current.toArray
      log s!"    sub-pool: {subPool.pool.size} unique subs, {subPool.hits} hits, {subPool.misses} misses"
      unless diagnostics do return some (k, summaryArr)
      -- h_contains check: every body branch PC's conjuncts are in the closure.
      -- Note: h_contains is about branchingLoopModel (= original body block
      -- summaries), NOT the composed fixpoint (summaryArr). The body branches'
      -- conjuncts are in the full closure by construction (extractClosure).
      -- Uses full closure (data + rip) since the abstract theory doesn't
      -- distinguish between guard types.
      do
        let (fullClosure, _, _) := extractClosure ip_reg bodyArr (dataOnly := false)
        let (fullPass, _, _, dataMissesF) := checkHContains ip_reg bodyArr fullClosure
        if fullPass then
          log s!"    [h_contains] PASS ({bodyArr.size} body branches, {fullClosure.size} closure PCs)"
        else
          log s!"    [h_contains] FAIL: {dataMissesF} data misses ({bodyArr.size} body branches)"
      -- Closedness check on BODY branches (branchingLoopModel).
      -- This is the check that matters for the certificate: are body branch
      -- substitutions closed over the full closure?
      do
        let (fullClosure2, _, _) := extractClosure ip_reg bodyArr (dataOnly := false)
        let mut bodyTrivClosed : Nat := 0
        let mut bodyNeedsSMT : Nat := 0
        let mut bodyViolations : Nat := 0
        let bodyTotal := bodyArr.size * fullClosure2.size
        for b in bodyArr do
          for phi in fullClosure2 do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => bodyTrivClosed := bodyTrivClosed + 1
            | some .true => bodyTrivClosed := bodyTrivClosed + 1
            | some pc' =>
              let inClosure := pc' == .true || fullClosure2.any (fun phi_j => phi_j == pc')
              if inClosure then
                bodyTrivClosed := bodyTrivClosed + 1
              else
                bodyNeedsSMT := bodyNeedsSMT + 1
        -- For non-trivial cases, run SMT equivalence check
        if bodyNeedsSMT > 0 then
          let mut smtPairs : Array (SymPC Reg × SymPC Reg) := #[]
          let mut smtLiftedIdx : Array Nat := #[]
          let mut liftedNeedingCheck2 : Array Nat := #[]
          let mut gIdx : Nat := 0
          for b in bodyArr do
            for phi in fullClosure2 do
              let lifted := substSymPC b.sub phi
              let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
              match SymPC.simplifyConst liftedSimplified with
              | none => pure ()
              | some .true => pure ()
              | some pc' =>
                let inClosure := pc' == .true || fullClosure2.any (fun phi_j => phi_j == pc')
                unless inClosure do
                  for phi_j in fullClosure2 do
                    smtPairs := smtPairs.push (pc', phi_j)
                    smtLiftedIdx := smtLiftedIdx.push gIdx
                  liftedNeedingCheck2 := liftedNeedingCheck2.push gIdx
              gIdx := gIdx + 1
          if smtPairs.size > 0 then
            let mut fwdP : Array (SymPC Reg × SymPC Reg) := #[]
            let mut revP : Array (SymPC Reg × SymPC Reg) := #[]
            for (cp, rp) in smtPairs do
              fwdP := fwdP.push (cp, rp)
              revP := revP.push (rp, cp)
            let (fwdR, _) ← smtCheckImplCached smtCache fwdP ".lake/smt_body_closed.smt2"
            let (revR, _) ← smtCheckImplCached smtCache revP ".lake/smt_body_closed.smt2"
            let mut closedBySMT2 : Std.HashSet Nat := {}
            for i in [:smtPairs.size] do
              if h1 : i < fwdR.size then
                if h2 : i < revR.size then
                  if fwdR[i] && revR[i] then
                    closedBySMT2 := closedBySMT2.insert smtLiftedIdx[i]!
            for gIdx2 in liftedNeedingCheck2 do
              unless closedBySMT2.contains gIdx2 do
                bodyViolations := bodyViolations + 1
        let bodyClosed := bodyViolations == 0
        if bodyClosed then
          log s!"    [body-closed] PASS: body branches closed over full closure ({bodyArr.size}×{fullClosure2.size}, trivial={bodyTrivClosed})"
        else
          log s!"    [body-closed] FAIL: {bodyViolations} violations ({bodyArr.size}×{fullClosure2.size}, trivial={bodyTrivClosed}, smt_cands={bodyNeedsSMT})"
      -- Task 1B: Closure closedness verification (on summaryArr, for reference).
      -- For each branch b in summaryArr and each data guard PC phi in closure:
      --   lifted = substSymPC b.sub phi  (the pc_lift from VexSummary/VexCompTree)
      --   simplified = simplifyLoadStorePC lifted |> SymPC.simplifyConst
      --   check: simplified ≡ some phi_j in closure, or trivially true/false
      do
        log s!"    [closedness] checking {summaryArr.size} branches × {closure.size} guards..."
        let mut trivClosedPairs : Nat := 0   -- simplified to true/false or syntactic match
        let mut needsSMTPairs : Nat := 0      -- require SMT semantic check
        -- SMT query data: for each lifted PC that fails syntactic check,
        -- compare against each phi_j in closure
        let mut closedQueryPairs : Array (SymPC Reg × SymPC Reg) := #[]
        let mut closedQueryLiftedIdx : Array Nat := #[]
        let mut liftedNeedingCheck : Array Nat := #[]  -- globalIdx of non-trivial lifted PCs
        let mut globalIdx : Nat := 0
        for b in summaryArr do
          for phi in closure do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none =>
              trivClosedPairs := trivClosedPairs + 1  -- false: unsatisfiable, trivially closed
            | some .true =>
              trivClosedPairs := trivClosedPairs + 1  -- true: trivially closed
            | some pc' =>
              -- Fast-path: syntactic match against closure
              let inClosure := pc' == .true || closure.any (fun phi_j => phi_j == pc')
              if inClosure then
                trivClosedPairs := trivClosedPairs + 1
              else
                -- Need SMT check: is pc' semantically equiv to some phi_j?
                for phi_j in closure do
                  closedQueryPairs := closedQueryPairs.push (pc', phi_j)
                  closedQueryLiftedIdx := closedQueryLiftedIdx.push globalIdx
                liftedNeedingCheck := liftedNeedingCheck.push globalIdx
                needsSMTPairs := needsSMTPairs + 1
            globalIdx := globalIdx + 1
        log s!"    [closedness] trivial={trivClosedPairs}/{globalIdx} smt_candidates={needsSMTPairs}"
        -- Run SMT semantic equivalence check via cached implication pairs.
        -- Equivalence (A ↔ B) = (A→B) ∧ (B→A): decompose into two implication queries.
        let mut closednessViolations : Nat := 0
        if closedQueryPairs.size > 0 then
          -- Build forward (cp→rp) and reverse (rp→cp) implication pairs
          let mut fwdPairs : Array (SymPC Reg × SymPC Reg) := #[]
          let mut revPairs : Array (SymPC Reg × SymPC Reg) := #[]
          for (cp, rp) in closedQueryPairs do
            fwdPairs := fwdPairs.push (cp, rp)
            revPairs := revPairs.push (rp, cp)
          let (fwdResults, fwdHits) ← smtCheckImplCached smtCache fwdPairs ".lake/smt_closedness.smt2"
          let (revResults, revHits) ← smtCheckImplCached smtCache revPairs ".lake/smt_closedness.smt2"
          -- A pair is equivalent iff both forward AND reverse implications hold
          let mut closedBySMT : Std.HashSet Nat := {}
          for i in [:closedQueryPairs.size] do
            if h1 : i < fwdResults.size then
              if h2 : i < revResults.size then
                if fwdResults[i] && revResults[i] then
                  closedBySMT := closedBySMT.insert closedQueryLiftedIdx[i]!
          -- Violations: lifted PCs not closed by SMT
          for gIdx in liftedNeedingCheck do
            unless closedBySMT.contains gIdx do
              closednessViolations := closednessViolations + 1
          let clTotalQueries := closedQueryPairs.size * 2
          log s!"    [closedness] smt: {clTotalQueries} queries (hits={fwdHits + revHits} misses={clTotalQueries - fwdHits - revHits}), {closedBySMT.size} closed, {closednessViolations} violations"
        let isClosed := closednessViolations == 0
        log s!"    [closedness] closure closed: {if isClosed then "YES" else "NO"}, violations={closednessViolations}"
      -- Diagnostic: dump closure PCs and non-closed lifted PCs for analysis
      do
        log s!"    [closure-diag] {closure.size} closure PCs:"
        let mut ci : Nat := 0
        for pc in closure do
          log s!"      φ[{ci}]: {SymPC.toSMTLib pc}  (loads={SymPC.hasLoad pc})"
          ci := ci + 1
        -- Dump first few non-closed lifted PCs
        let mut dumpCount : Nat := 0
        let mut b_idx : Nat := 0
        for b in summaryArr do
          let mut phi_idx : Nat := 0
          for phi in closure do
            if dumpCount < 10 then
              let lifted := substSymPC b.sub phi
              let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
              match SymPC.simplifyConst liftedSimplified with
              | none => pure ()  -- trivial false
              | some .true => pure ()  -- trivial true
              | some pc' =>
                -- Check if it matches any closure member
                let mut matched := false
                for phi_j in closure do
                  if phi_j == pc' then matched := true
                unless matched do
                  log s!"      NONCLOSED b[{b_idx}]×φ[{phi_idx}]: {SymPC.toSMTLib pc'}"
                  log s!"        original guard: {SymPC.toSMTLib phi}"
                  log s!"        loads={SymPC.hasLoad pc'}"
                  dumpCount := dumpCount + 1
            phi_idx := phi_idx + 1
          b_idx := b_idx + 1
        log s!"    [closure-diag] showed {dumpCount} non-closed lifted PCs (first 10)"
      -- Phase 2: Template basis SemClosed experiment.
      -- Anti-unify non-closed lifted PCs with originals to discover template structure,
      -- then check if one round of basis expansion makes SemClosed pass.
      do
        -- Step 1: Collect all non-closed lifted PCs with their originals
        let mut nonClosedLifted : Array (SymPC Reg) := #[]
        let mut nonClosedOriginals : Array (SymPC Reg) := #[]
        for b in summaryArr do
          for phi in closure do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => pure ()  -- trivial false
            | some .true => pure ()  -- trivial true
            | some pc' =>
              let inClosure := pc' == .true || closure.any (fun phi_j => phi_j == pc')
              unless inClosure do
                nonClosedLifted := nonClosedLifted.push pc'
                nonClosedOriginals := nonClosedOriginals.push phi
        log s!"    [template-exp] {nonClosedLifted.size} non-closed lifted PCs from {summaryArr.size}×{closure.size} pairs"
        -- Step 2: Anti-unify each (original, lifted) pair to discover template structure
        if nonClosedLifted.size > 0 then
          let mut totalHoles : Nat := 0
          let mut maxHoles : Nat := 0
          let paired := nonClosedOriginals.zip nonClosedLifted
          for (orig, lifted) in paired do
            let (template, _subs) := antiUnify orig lifted
            let holes := template.holeCount
            totalHoles := totalHoles + holes
            if holes > maxHoles then maxHoles := holes
          log s!"    [template-exp] anti-unification: avg_holes={totalHoles / nonClosedLifted.size} max_holes={maxHoles}"
          -- Step 3: Build expanded basis = closure ∪ non-closed lifted PCs (deduped)
          let mut expandedBasis : Array (SymPC Reg) := closure
          let mut seen : Std.HashSet (SymPC Reg) :=
            closure.foldl (fun s pc => s.insert pc) {}
          for pc in nonClosedLifted do
            unless seen.contains pc do
              seen := seen.insert pc
              expandedBasis := expandedBasis.push pc
          log s!"    [template-exp] expanded basis: {expandedBasis.size} PCs (was {closure.size})"
          -- Step 4: Re-check SemClosed against expanded basis.
          -- For each branch b and each φ in expanded basis, is substSymPC b.sub φ
          -- determined by the expanded basis? (Two-state CVC5 query)
          let mut expandedLiftedPCs : Array (SymPC Reg) := #[]
          let mut expandedTrivial : Nat := 0
          for b in summaryArr do
            for phi in expandedBasis do
              let lifted := substSymPC b.sub phi
              let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
              match SymPC.simplifyConst liftedSimplified with
              | none => expandedTrivial := expandedTrivial + 1
              | some .true => expandedTrivial := expandedTrivial + 1
              | some pc' =>
                let inBasis := expandedBasis.any (fun phi_j => phi_j == pc')
                if inBasis then
                  expandedTrivial := expandedTrivial + 1
                else
                  expandedLiftedPCs := expandedLiftedPCs.push pc'
          let totalPairs := summaryArr.size * expandedBasis.size
          log s!"    [template-exp] expanded SemClosed: trivial={expandedTrivial}/{totalPairs} smt_candidates={expandedLiftedPCs.size}"
          if expandedLiftedPCs.size > 0 then
            let results ← smtCheckSemClosedBatch expandedLiftedPCs expandedBasis log
            let violations := results.filter (· == false) |>.size
            log s!"    [template-exp] RESULT: {violations} violations out of {expandedLiftedPCs.size} SMT checks"
            if violations == 0 then
              log s!"    [template-exp] *** ONE-ROUND EXPANSION SUFFICES — template basis gives SemClosed ***"
            else
              log s!"    [template-exp] *** Template basis INSUFFICIENT — need approach D (memory regions) ***"
          else
            log s!"    [template-exp] *** ALL TRIVIALLY CLOSED — template basis gives SemClosed ***"
      -- Atom-closure check (approach B): does the expanded basis satisfy
      -- h_atoms_closed from semClosed_of_liftedAtomsInBasis?
      -- If yes: SemClosed holds by structural theorem, no SMT needed.
      do
        -- Build expanded basis for body branches (branchingLoopModel)
        let (fullClosure3, _, _) := extractClosure ip_reg bodyArr (dataOnly := false)
        -- One-round expansion on body branches
        let mut atomBasis : Array (SymPC Reg) := fullClosure3
        let mut atomSeen : Std.HashSet (SymPC Reg) :=
          fullClosure3.foldl (fun s pc => s.insert pc) {}
        -- Add full branch PCs for h_contains
        for b in bodyArr do
          unless atomSeen.contains b.pc do
            atomSeen := atomSeen.insert b.pc
            atomBasis := atomBasis.push b.pc
        -- Add non-closed lifted PCs (one round)
        for b in bodyArr do
          for phi in fullClosure3 do
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => pure ()
            | some .true => pure ()
            | some pc' =>
              unless atomSeen.contains pc' do
                atomSeen := atomSeen.insert pc'
                atomBasis := atomBasis.push pc'
        -- Now check: for each body branch and expanded basis PC,
        -- are all atoms of the lifted PC in the expanded basis?
        let mut atomViolations : Nat := 0
        let mut atomTotal : Nat := 0
        let atomBasisSet : Std.HashSet (SymPC Reg) :=
          atomBasis.foldl (fun s pc => s.insert pc) {}
        for b in bodyArr do
          for phi in atomBasis do
            atomTotal := atomTotal + 1
            let lifted := substSymPC b.sub phi
            let liftedSimplified := simplifyLoadStorePCOpt addrClassify lifted
            match SymPC.simplifyConst liftedSimplified with
            | none => pure ()  -- trivial false, atoms vacuously in basis
            | some .true => pure ()  -- trivial true, no atoms
            | some pc' =>
              for a in SymPC.atoms pc' do
                unless atomBasisSet.contains a do
                  atomViolations := atomViolations + 1
        if atomViolations == 0 then
          log s!"    [atom-closed] PASS: expanded basis is atom-closed ({atomBasis.size} PCs, {atomTotal} pairs checked)"
          log s!"    [atom-closed] *** semClosed_of_liftedAtomsInBasis applies — SemClosed by structural theorem ***"
        else
          log s!"    [atom-closed] FAIL: {atomViolations} atom violations ({atomBasis.size} PCs, {atomTotal} pairs)"
      return some (k, summaryArr)
    frontier := newBranches
  return none

/-- Split body branches into non-call (kept in body) and call-expanded
    (seeded into initial frontier).

    For each body branch B:
    - If B's rip target matches a function entry with a summary:
      Compose B with each summary branch → add to callResults (initial frontier)
      B is REMOVED from the body.
    - Otherwise: B stays in the body for iterative composition.

    This prevents re-expansion: summary results are in the initial frontier,
    and the body only contains the function's own non-call blocks. Each
    iteration composes non-call blocks with frontier — no expression nesting. -/
def splitBodyAndExpandCalls {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg)
    (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg)))) :
    (Array (Branch (SymSub Reg) (SymPC Reg))  -- nonCallBody (for iterative composition)
    × Array (Branch (SymSub Reg) (SymPC Reg))  -- callResults (initial frontier seed)
    × Nat × Nat × Nat) := Id.run do  -- callsExpanded, branchesAdded, dropped
  let isa := vexSummaryISA Reg
  let mut nonCallBody : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut callResults : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut callsExpanded : Nat := 0
  let mut branchesAdded : Nat := 0
  let mut dropped : Nat := 0
  for b in bodyArr do
    match extractRipTarget ip_reg b.sub with
    | some target =>
      match summaries.get? target with
      | some summaryBranches =>
        callsExpanded := callsExpanded + 1
        for sb in summaryBranches do
          let composed := b.compose isa sb
          match simplifyBranch composed with
          | none => dropped := dropped + 1
          | some b' =>
            callResults := callResults.push b'
            branchesAdded := branchesAdded + 1
      | none =>
        nonCallBody := nonCallBody.push b
    | none =>
      nonCallBody := nonCallBody.push b
  return (nonCallBody, callResults, callsExpanded, branchesAdded, dropped)
