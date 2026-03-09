# Next Priorities (2026-03-09 14:27:26 PDT)

## Current state

The VEX fragment now has:
- explicit syntax-summary-concrete bridge
- width support through `lt64`/`le64`, shifts, bitwise ops, `sext8to32`
- `SemClosed` / `Refinement.lean`
- end-to-end tier redesign through Phase 5
- toy STS1-style examples through Tier 7
- witness-first loop packaging and deterministic-route bridge points

The opcode grind is progressing in parallel. That is not the current bottleneck.

## Priority order

1. **Fetched CFG / subsystem theorem path**
   - Why: this is the missing middle layer between isolated path theorems and real extracted subsystems from binaries.
   - Deliverable: a small theorem/API that packages a fetched program region and connects it to finite path-family witnesses.
   - Status: initial theorem/API added in `Instances/ISAs/VexSubsystem.lean`.
     The repo now has `FetchedSubsystemWitness` and the adequacy theorem
     `extractedModel_of_fetchedSubsystemWitness`. Next step is a nontrivial
     fetched-subsystem example or stronger region packaging.

2. **Refinement-backed subsystem theorem**
   - Why: `Refinement.lean` exists, but the non-toy subsystem-level STS1 story is still not packaged cleanly.
   - Deliverable: one real subsystem theorem/example that uses the refinement pipeline on a fetched multi-block program region.
   - Status: unblocked by the fetched-subsystem witness layer. This is now the
     next theorem/example target.

3. **Byte-width path (`load8`, byte extensions)**
   - Why: this is the main realism gap for parser-like binaries.
   - Deliverable: byte-width memory/load/extension support plus one real fixture.
   - Status: deferred until the fetched-subsystem layer is cleaner.

4. **Witness-first convergence over realistic regions**
   - Why: the theorem scaffolding exists, but we still need the right complete-witness existence theorem for a meaningful loop/subsystem class.
   - Deliverable: discharge `LoopWitnessComplete` or its region analogue from a real finite/stabilization argument.
   - Status: open theory problem, not the first move.

## Immediate task

Define the smallest useful fetched-subsystem object and prove one nontrivial adequacy theorem for it.

The target shape is:
- a finite fetched program or region
- a finite family of valid fetched paths through it
- a theorem that the extracted summary family is adequate for that fetched subsystem behavior

This should sit strictly above `ExtractiblePathFamilyModel` / `ExtractibleProgramTrace`, and strictly below the full convergence story.
