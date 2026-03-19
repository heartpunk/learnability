import Instances.ISAs.DispatchLoopEval

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-! ## Path History — ordered composition event tracking

Branches carry an append-only path history alongside the flat PC. The flat
`pc` field remains for all existing uses (dedup, simplification, SMT, hashing).
The `history` field preserves the sequential ordering of composition events
for grammar extraction: which guards were encountered, which functions were
called/returned, and in what order.

PathHistory is a cons-list (persistent/immutable). Branches sharing a common
prefix (same body branch composed with different frontier branches) share the
prefix in memory. Cost per branch: O(composition depth) extra pointers. -/

/-- A path event: what happened at a composition step. -/
inductive PathEvent (Reg : Type) where
  | guard : SymPC Reg → PathEvent Reg       -- a PC guard encountered
  | call : UInt64 → PathEvent Reg           -- called function at this address
  | ret : UInt64 → PathEvent Reg            -- returned from function
  | entry : UInt64 → PathEvent Reg          -- entered this function

/-- Persistent path history — cons-list for prefix sharing. -/
inductive PathHistory (Reg : Type) where
  | root : PathHistory Reg
  | cons : PathEvent Reg → PathHistory Reg → PathHistory Reg

/-- Convert path history to array (most recent event first). -/
def PathHistory.toArray {Reg : Type} : PathHistory Reg → Array (PathEvent Reg)
  | .root => #[]
  | .cons e h => #[e] ++ h.toArray

/-- Length of path history. -/
def PathHistory.length {Reg : Type} : PathHistory Reg → Nat
  | .root => 0
  | .cons _ h => 1 + h.length

/-- Append a guard event to the history. -/
def PathHistory.guard {Reg : Type} (pc : SymPC Reg) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.guard pc) h

/-- Append a call event to the history. -/
def PathHistory.call {Reg : Type} (target : UInt64) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.call target) h

/-- Append a return event to the history. -/
def PathHistory.ret {Reg : Type} (target : UInt64) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.ret target) h

/-- Append an entry event to the history. -/
def PathHistory.entry {Reg : Type} (addr : UInt64) (h : PathHistory Reg) : PathHistory Reg :=
  .cons (.entry addr) h

/-- Split body branches into non-call (kept in body) and call-expanded
    (seeded into initial frontier), with path history tracking.

    Like `splitBodyAndExpandCalls` but records `.call target` and `.ret target`
    events on each call-expanded branch, preserving the sequential call order
    for grammar extraction. -/
def splitBodyAndExpandCallsH {Reg : Type} [DecidableEq Reg] [Fintype Reg] [BEq Reg]
    (ip_reg : Reg)
    (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg)))) :
    (Array (Branch (SymSub Reg) (SymPC Reg))  -- nonCallBody
    × Array (Branch (SymSub Reg) (SymPC Reg) × PathHistory Reg)  -- callResults with history
    × Nat × Nat × Nat) := Id.run do  -- callsExpanded, branchesAdded, dropped
  let isa := vexSummaryISA Reg
  let mut nonCallBody : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
  let mut callResults : Array (Branch (SymSub Reg) (SymPC Reg) × PathHistory Reg) := #[]
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
            -- Record call → guard → ret in history (most recent first in cons-list)
            let hist := PathHistory.root
              |>.call target
              |>.guard (isa.pc_lift b.sub sb.pc)
              |>.ret target
            callResults := callResults.push (b', hist)
            branchesAdded := branchesAdded + 1
      | none =>
        nonCallBody := nonCallBody.push b
    | none =>
      nonCallBody := nonCallBody.push b
  return (nonCallBody, callResults, callsExpanded, branchesAdded, dropped)

/-- Per-function stabilization with optional initial frontier seeding.
    When initialFrontier is non-empty, those branches are added to the
    initial state (along with skip) instead of starting from skip alone.
    This is used to seed call-expanded results into the frontier without
    putting them in the body (which would cause expression nesting). -/
def computeFunctionStabilization {Reg : Type} [DecidableEq Reg] [Fintype Reg] [Hashable Reg] [EnumReg Reg] [BEq Reg] [ToString Reg]
    (ip_reg : Reg) (bodyArr : Array (Branch (SymSub Reg) (SymPC Reg)))
    (summaries : Std.HashMap UInt64 (Array (Branch (SymSub Reg) (SymPC Reg))))
    (maxIter : Nat) (log : String → IO Unit)
    (smtCache : IO.Ref SMTCache)
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
  current := current.insert initBranch
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
  let mut convRepPCs     : Array (SymPC Reg)          := #[initBranch.pc]
  let mut convRepSynSigs : Array (List Bool)           := #[computePCSignature closure initBranch.pc]
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
        convRepSynSigs := convRepSynSigs.push (computePCSignature closure zb'.pc)
        convRepSemSigs := convRepSemSigs.push none
        frontier := frontier.push zb'
  -- Seed initial frontier into current set
  for b in frontier do
    current := current.insert b
  log s!"    initial frontier: {frontier.size} branches (skip + {initialFrontier.size} call-expanded)"
  for k in List.range maxIter do
    let t_start ← IO.monoMsNow
    -- Pure composition: no summary interception, body has no call branches
    let (composedTagged, pairsComposed, skipped, dropped) :=
      composeBranchArrayIndexed ip_reg bodyArr frontier
    -- Strip body indices (not used in this function)
    let composed := composedTagged.map (·.1)
    -- Simplify: load-after-store + constant folding + zero non-projected
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
    let mut newBranches : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    let mut dupes : Nat := 0
    -- Phase 1: structural dedup — collect all branches not already in current
    let mut semCands : Array (Branch (SymSub Reg) (SymPC Reg)) := #[]
    for b in simplified do
      if current.contains b then
        dupes := dupes + 1
      else
        current := current.insert b  -- ALL structurally distinct branches kept for summary
        semCands := semCands.push b
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
    if semCands.size > 0 then
      -- Compute syntactic sigs for all candidates
      let candSynSigs := semCands.map (fun c => computePCSignature closure c.pc)
      -- Fast path: which candidates have a syntactic sig matching an existing rep?
      let mut synMatched : Std.HashSet Nat := {}
      for ci in [:semCands.size] do
        let csig := candSynSigs[ci]!
        let mut ri := 0
        while ri < convRepSynSigs.size do
          if convRepSynSigs[ri]! == csig then
            synMatched := synMatched.insert ci
            ri := convRepSynSigs.size  -- break
          ri := ri + 1
      -- Collect SMT candidates: those with no syntactic match
      let mut smtCandIdxs : Array Nat := #[]
      for ci in [:semCands.size] do
        unless synMatched.contains ci do
          smtCandIdxs := smtCandIdxs.push ci
      -- Semantic path: only if there are unmatched candidates and closure is non-empty
      let mut candSemSigsArr : Array (Option (Array Bool)) := Array.replicate semCands.size none
      let mut totalSMTQueries := 0
      let mut totalSMTCacheHits := 0
      let mut semMatched : Std.HashSet Nat := {}
      if smtCandIdxs.size > 0 && closure.size > 0 then
        let n := closure.size
        -- Build batch of PCs needing semantic sig computation:
        -- (1) reps with uncomputed sem sigs, (2) SMT candidate branch PCs.
        -- Use Array.extract to avoid [i]! on SymPC/Branch arrays.
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
            batchCandIdxs := batchCandIdxs.push 0  -- dummy
          | _ => pure ()
        for ci in smtCandIdxs do
          for b in semCands.extract ci (ci + 1) do
            batchPCs := batchPCs.push b.pc
          batchIsRep    := batchIsRep.push false
          batchRepIdxs  := batchRepIdxs.push 0  -- dummy
          batchCandIdxs := batchCandIdxs.push ci
        -- Batch CVC5 with caching: for each pc in batchPCs, n queries (one per closure PC).
        let mut convPairs : Array (SymPC Reg × SymPC Reg) := #[]
        for pc in batchPCs do
          for phi in closure do
            convPairs := convPairs.push (pc, phi)
        let (allSemResults, convHits) ← smtCheckImplCached smtCache convPairs ".lake/smt_semsig.smt2"
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
      log s!"    smt conv: {totalSMTQueries}q (hits={totalSMTCacheHits} misses={totalSMTQueries - totalSMTCacheHits}) → syn-collapsed={synMatched.size} sem-collapsed={semMatched.size}"
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

def stratifiedFixpoint
    (functions : Array FunctionSpec)
    (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    (maxIter : Nat := 200) :
    IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  -- Build address classifier from ELF memory regions.
  -- rsp and rbp are stack registers — addresses relative to them are in the
  -- stack region, which doesn't overlap any loaded ELF section.
  let addrClassify : Option (AddrClassifier Amd64Reg) :=
    if regions.size > 0 then
      some (classifyAddr regions [Amd64Reg.rsp, Amd64Reg.rbp])
    else none
  -- Parse all function blocks into raw body arrays
  let mut funcBlocks : Array (String × Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := #[]
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error e =>
      log s!"  PARSE ERROR for {func.name}: {e}"
      return {}
    | .ok pairs =>
      let body := flatBodyDenot ip_reg pairs
      let bodyArr := finsetToArray body
      funcBlocks := funcBlocks.push (func.name, bodyArr)
      log s!"  {func.name} @ 0x{String.ofList (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches"
  -- Phase 1: Compute leaf function (next_sym) fixpoint — no summaries needed
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  -- Green-style SMT query cache: shared across all function stabilizations
  let smtCache ← IO.mkRef ({} : SMTCache)
  log s!"\n--- Phase 1: Leaf function (next_sym) ---"
  let t0 ← IO.monoMsNow
  let (nextSymName, nextSymBody) := funcBlocks[0]!
  -- Use computeFunctionStabilization directly (returns branch array as summary).
  -- Don't double-run with computeStabilizationHS — that keeps two copies of deeply-nested
  -- symbolic branches alive simultaneously, causing OOM.
  match ← computeFunctionStabilization ip_reg nextSymBody {} maxIter log smtCache (addrClassify := addrClassify) (maxBranches := maxBranches) (diagnostics := diagnostics) with
  | some (k, summaryArr) =>
    let t1 ← IO.monoMsNow
    summaries := summaries.insert functions[0]!.entryAddr summaryArr
    log s!"  {nextSymName}: converged at K={k}, {summaryArr.size} summary branches, {t1 - t0}ms"
  | none =>
    log s!"  {nextSymName}: DID NOT CONVERGE"
    return {}
  -- Phase 2: Iterate NT function summaries to fixpoint
  -- At each outer round, for each NT function:
  --   1. Split body into non-call blocks + call-expanded results (via splitBodyAndExpandCalls)
  --   2. Run stabilization on non-call body, seeding call results as initial frontier
  --   3. The converged set = new function summary
  -- Key: non-call body never contains summary-expanded branches, preventing expression nesting
  log s!"\n--- Phase 2: NT functions (mutual recursion) ---"
  -- Initialize NT summaries as empty
  for i in [1:functions.size] do
    summaries := summaries.insert functions[i]!.entryAddr #[]
  let mut outerRound : Nat := 0
  let mut outerChanged := true
  while outerChanged do
    outerChanged := false
    outerRound := outerRound + 1
    log s!"\n  === Outer round {outerRound} ==="
    for i in [1:functions.size] do
      let func := functions[i]!
      let (fname, rawBody) := funcBlocks[i]!
      let t0 ← IO.monoMsNow
      -- Step 1: Split body into non-call blocks + call-expanded results
      let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
        splitBodyAndExpandCalls ip_reg rawBody summaries
      log s!"    {fname}: split body {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, {branchesAdded} branches, {droppedExp} dropped)"
      -- Step 2: Run stabilization on non-call body, seeding call results as initial frontier
      let oldSummary := summaries.getD func.entryAddr #[]
      match ← computeFunctionStabilization ip_reg nonCallBody {} (min maxIter 30) log smtCache (initialFrontier := callResults) (addrClassify := addrClassify) (maxBranches := maxBranches) (diagnostics := diagnostics) with
      | some (k, newSummary) =>
        let t1 ← IO.monoMsNow
        if newSummary.size != oldSummary.size then
          outerChanged := true
          summaries := summaries.insert func.entryAddr newSummary
          log s!"  {fname}: K={k}, {newSummary.size} branches (was {oldSummary.size}), {t1 - t0}ms [CHANGED]"
        else
          log s!"  {fname}: K={k}, {newSummary.size} branches (stable), {t1 - t0}ms"
      | none =>
        log s!"  {fname}: DID NOT CONVERGE"
        return {}
  log s!"\n=== Stratified fixpoint complete after {outerRound} outer rounds ==="
  for i in [:functions.size] do
    let func := functions[i]!
    let summary := summaries.getD func.entryAddr #[]
    log s!"  {func.name}: {summary.size} branches"
  -- SMT cache summary
  let cacheContents ← smtCache.get
  log s!"\n=== SMT Cache Summary ==="
  log s!"  cache entries: {cacheContents.size}"
  return summaries

/-! ## Weak Topological Ordering (Bourdoncle's Algorithm)

Bourdoncle's hierarchical decomposition ("Efficient Chaotic Iteration
Strategies with Widenings", 1993) computes the optimal iteration structure
for fixpoint computation over a call graph.

- Trivial SCCs (single vertex, no self-loop) → `WTOElem.vertex`
- Non-trivial SCCs → select head (first DFS-visited), recursively compute
  WTO of the SCC body, wrap in `WTOElem.component head body`

The recursive iteration strategy (Theorem 5): only check the **head** of each
component for stabilization — if the head hasn't changed, the whole component
is stable. For nested mutual recursion, inner loops converge before outer
loops re-iterate. -/

/-- A WTO element: either a single vertex or a component (head + body). -/
inductive WTOElem where
  | vertex : UInt64 → WTOElem
  | component : UInt64 → Array WTOElem → WTOElem
  deriving Inhabited

/-- Get the head address of a WTO element. -/
def WTOElem.head : WTOElem → UInt64
  | .vertex addr => addr
  | .component addr _ => addr

/-- DFS frame for iterative Tarjan: (node, successor_index, min_dfn). -/
structure TarjanFrame where
  node : UInt64
  succIdx : Nat
  minDfn : Nat
  deriving Inhabited

/-- Bourdoncle's WTO via modified Tarjan's SCC algorithm.
    Returns the WTO as an array of elements in topological order.
    Fuel bounds recursion depth (≤ number of nodes); never exhausted in practice. -/
def computeWTO (nodes : Array UInt64) (edges : Array (UInt64 × UInt64))
    (root : UInt64) (fuel : Nat := nodes.size + 1) : Array WTOElem :=
  match fuel with
  | 0 => #[]
  | fuel + 1 => Id.run do
  -- Adjacency list
  let mut adj : Std.HashMap UInt64 (Array UInt64) := {}
  for (src, tgt) in edges do
    adj := adj.insert src ((adj.getD src #[]).push tgt)
  -- DFS state
  let mut dfn : Std.HashMap UInt64 Nat := {}
  let mut num : Nat := 0
  let mut stack : Array UInt64 := #[]
  let mut onStack : Std.HashSet UInt64 := {}
  let mut result : Array WTOElem := #[]
  -- The node set for quick membership checks
  let nodeSet : Std.HashSet UInt64 := nodes.foldl (fun s n => s.insert n) {}
  let mut workStack : Array TarjanFrame := #[]
  -- Process starting from root, then any unreachable nodes
  let mut toVisit : Array UInt64 := #[root]
  for n in nodes do
    unless n == root do toVisit := toVisit.push n
  for startNode in toVisit do
    if dfn.contains startNode then continue
    -- Push initial frame
    num := num + 1
    dfn := dfn.insert startNode num
    stack := stack.push startNode
    onStack := onStack.insert startNode
    workStack := workStack.push ⟨startNode, 0, num⟩
    while !workStack.isEmpty do
      let frame := workStack.back!
      let succs := adj.getD frame.node #[]
      if frame.succIdx < succs.size then
        let succ := succs[frame.succIdx]!
        -- Advance successor index
        workStack := workStack.pop.push { frame with succIdx := frame.succIdx + 1 }
        if !nodeSet.contains succ then
          continue  -- skip edges to nodes outside our scope
        if !dfn.contains succ then
          -- Tree edge: visit successor
          num := num + 1
          dfn := dfn.insert succ num
          stack := stack.push succ
          onStack := onStack.insert succ
          workStack := workStack.push ⟨succ, 0, num⟩
        else if onStack.contains succ then
          -- Back edge: update min
          let succDfn := dfn.getD succ 0
          let curFrame := workStack.back!
          if succDfn < curFrame.minDfn then
            workStack := workStack.pop.push { curFrame with minDfn := succDfn }
      else
        -- All successors processed
        workStack := workStack.pop
        let nodeDfn := dfn.getD frame.node 0
        if frame.minDfn == nodeDfn then
          -- SCC head: pop the component from stack
          let mut component : Array UInt64 := #[]
          while !stack.isEmpty do
            let top := stack.back!
            stack := stack.pop
            onStack := onStack.erase top
            component := component.push top
            if top == frame.node then break
          if component.size == 1 then
            -- Check for self-loop
            let hasSelfLoop := (adj.getD frame.node #[]).any (· == frame.node)
            if hasSelfLoop then
              result := result.push (.component frame.node #[])
            else
              result := result.push (.vertex frame.node)
          else
            -- Non-trivial SCC: head is frame.node, rest are body
            -- Recursively compute WTO of the body members
            let bodyNodes := component.filter (· != frame.node)
            let bodyEdges := edges.filter fun (s, t) =>
              bodyNodes.any (· == s) && (bodyNodes.any (· == t) || t == frame.node)
            let bodyWTO := computeWTO bodyNodes bodyEdges frame.node fuel
            result := result.push (.component frame.node bodyWTO)
        else
          -- Propagate min to parent
          if !workStack.isEmpty then
            let parent := workStack.back!
            if frame.minDfn < parent.minDfn then
              workStack := workStack.pop.push { parent with minDfn := frame.minDfn }
  return result
termination_by fuel

/-- Pretty-print a WTO for logging. -/
partial def ppWTO (elems : Array WTOElem)
    (nameOf : UInt64 → String := fun a => s!"0x{String.ofList (Nat.toDigits 16 a.toNat)}") :
    String :=
  let rec ppElem : WTOElem → String
    | .vertex addr => nameOf addr
    | .component head body =>
      let bodyStr := ", ".intercalate (body.toList.map ppElem)
      s!"({nameOf head} {bodyStr})"
  " ".intercalate (elems.toList.map ppElem)

/-! ## WTO-based Fixpoint

Replaces the hardcoded 2-phase `stratifiedFixpoint` with a generic N-phase
structure driven by the WTO of the call graph. The convergence theorem
doesn't care about lexer/NT classification — it just needs summaries
available when composing.

Implements Bourdoncle's recursive iteration strategy:
- `vertex f` → analyze f once with current summaries
- `component head body` → repeat { analyze head; interpretWTO body }
  until head's summary stabilizes -/

/-- Flatten a WTO into a work-list for iterative interpretation.
    Each entry: (addr, isComponentHead, componentBodyElems).
    Component heads get `some body`; vertices get `none`. -/
def flattenWTOWork : Array WTOElem → Array (UInt64 × Option (Array WTOElem))
  | elems => elems.foldl (fun acc e => match e with
    | .vertex addr => acc.push (addr, none)
    | .component head body => acc.push (head, some body)) #[]

/-- WTO-driven fixpoint: analyze functions in weak topological order.
    For each vertex, analyze once. For each component, iterate until
    the head's summary stabilizes. -/
def wtoFixpoint
    (functions : Array FunctionSpec)
    (wto : Array WTOElem)
    (regions : Array MemRegion := #[])
    (log : String → IO Unit)
    (maxIter : Nat := 200)
    (maxBranches : Nat := 10000)
    (diagnostics : Bool := false)
    : IO (Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg)))) := do
  let ip_reg := Amd64Reg.rip
  let addrClassify : Option (AddrClassifier Amd64Reg) :=
    if regions.size > 0 then
      some (classifyAddr regions [Amd64Reg.rsp, Amd64Reg.rbp])
    else none
  -- Parse all function blocks into raw body arrays
  let mut funcBlocks : Std.HashMap UInt64 (String × Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  for func in functions do
    match parseBlocksWithAddresses func.blocks with
    | .error e =>
      log s!"  PARSE ERROR for {func.name}: {e}"
      return {}
    | .ok pairs =>
      let body := flatBodyDenot ip_reg pairs
      let bodyArr := finsetToArray body
      funcBlocks := funcBlocks.insert func.entryAddr (func.name, bodyArr)
      log s!"  {func.name} @ 0x{String.ofList (Nat.toDigits 16 func.entryAddr.toNat)}: {pairs.length} blocks, {bodyArr.size} body branches"
  -- Initialize all summaries as empty
  let mut summaries : Std.HashMap UInt64 (Array (Branch (SymSub Amd64Reg) (SymPC Amd64Reg))) := {}
  for func in functions do
    summaries := summaries.insert func.entryAddr #[]
  -- Shared SMT cache
  let smtCache ← IO.mkRef ({} : SMTCache)
  -- Name lookup for logging
  let nameOf (addr : UInt64) : String :=
    match functions.find? (·.entryAddr == addr) with
    | some f => f.name
    | none => s!"0x{String.ofList (Nat.toDigits 16 addr.toNat)}"
  log s!"\n=== WTO Fixpoint ==="
  log s!"  WTO: {ppWTO wto nameOf}"
  -- Process top-level WTO elements
  for elem in wto do
    match elem with
    | .vertex addr =>
      log s!"\n  --- vertex: {nameOf addr} ---"
      match funcBlocks.get? addr with
      | none => pure ()
      | some (fname, rawBody) =>
        let t0 ← IO.monoMsNow
        let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
          splitBodyAndExpandCalls ip_reg rawBody summaries
        log s!"    {fname}: split {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, +{branchesAdded}, -{droppedExp})"
        match ← computeFunctionStabilization ip_reg nonCallBody {} maxIter log smtCache
            (initialFrontier := callResults) (addrClassify := addrClassify)
            (maxBranches := maxBranches) (diagnostics := diagnostics) with
        | some (k, summaryArr) =>
          let t1 ← IO.monoMsNow
          log s!"    {fname}: converged K={k}, {summaryArr.size} branches, {t1 - t0}ms"
          summaries := summaries.insert addr summaryArr
        | none =>
          log s!"    {fname}: DID NOT CONVERGE"
    | .component head body =>
      log s!"\n  === component head: {nameOf head} ==="
      -- Bourdoncle's recursive strategy: iterate {head; body} until head stabilizes
      -- For nested components in body, we flatten: analyze each body element once per round
      let bodyWork := flattenWTOWork body
      let mut round : Nat := 0
      let mut stable := false
      while !stable && round < maxIter do
        round := round + 1
        log s!"\n  --- component round {round}, head: {nameOf head} ---"
        let oldSize := (summaries.getD head #[]).size
        -- Analyze head
        match funcBlocks.get? head with
        | none => stable := true
        | some (fname, rawBody) =>
          let t0 ← IO.monoMsNow
          let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
            splitBodyAndExpandCalls ip_reg rawBody summaries
          log s!"    {fname}: split {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, +{branchesAdded}, -{droppedExp})"
          match ← computeFunctionStabilization ip_reg nonCallBody {} maxIter log smtCache
              (initialFrontier := callResults) (addrClassify := addrClassify)
              (maxBranches := maxBranches) (diagnostics := diagnostics) with
          | some (k, summaryArr) =>
            let t1 ← IO.monoMsNow
            log s!"    {fname}: converged K={k}, {summaryArr.size} branches, {t1 - t0}ms"
            summaries := summaries.insert head summaryArr
          | none =>
            log s!"    {fname}: DID NOT CONVERGE"
            stable := true  -- bail on divergence
        -- Analyze body elements
        for (addr, nested) in bodyWork do
          match funcBlocks.get? addr with
          | none => pure ()
          | some (fname, rawBody) =>
            let t0 ← IO.monoMsNow
            let (nonCallBody, callResults, callsExp, branchesAdded, droppedExp) :=
              splitBodyAndExpandCalls ip_reg rawBody summaries
            log s!"    {fname}: split {rawBody.size} → {nonCallBody.size} non-call + {callResults.size} call-expanded ({callsExp} calls, +{branchesAdded}, -{droppedExp})"
            -- Nested component heads get iterated too
            let iterLimit := match nested with
              | some _ => maxIter  -- nested component head: may need iteration
              | none => maxIter
            match ← computeFunctionStabilization ip_reg nonCallBody {} iterLimit log smtCache
                (initialFrontier := callResults) (addrClassify := addrClassify)
                (maxBranches := maxBranches) (diagnostics := diagnostics) with
            | some (k, summaryArr) =>
              let t1 ← IO.monoMsNow
              log s!"    {fname}: converged K={k}, {summaryArr.size} branches, {t1 - t0}ms"
              summaries := summaries.insert addr summaryArr
            | none =>
              log s!"    {fname}: DID NOT CONVERGE"
        -- Check if head stabilized
        let newSize := (summaries.getD head #[]).size
        if newSize == oldSize then
          stable := true
          log s!"  component head {nameOf head} stable after {round} rounds"
  log s!"\n=== WTO Fixpoint complete ==="
  for func in functions do
    let summary := summaries.getD func.entryAddr #[]
    log s!"  {func.name}: {summary.size} branches"
  let cacheContents ← smtCache.get
  log s!"\n=== SMT Cache Summary ==="
  log s!"  cache entries: {cacheContents.size}"
  return summaries

