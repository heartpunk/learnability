import SymExec.Refinement

/-!
# Dispatch Structure Certificate

Post-extraction certification artifact validating a pre-extraction
dispatch-structure hypothesis.

A designer who knows their system is a dispatch loop (parser, interpreter,
protocol handler, terminal emulator, etc.) runs the extraction pipeline.
If the pipeline succeeds, it produces this certificate: an extracted model,
a predicate basis, and a proof that the basis is pullback-closed (SemClosed).

The pullback closure property is the mathematical core:
- Ranzato & Tapparo 2004: forward completeness = strong preservation
- Graf & Saidi 1997: closure under weakest precondition = exact abstraction
- HMR05: STS1 = finite pre+Boolean closure

The quotient induced by the basis has at most 2^|basis| states and is
bisimilar to the concrete system.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Post-extraction certification artifact validating a pre-extraction
    dispatch-structure hypothesis.

    A designer who knows their system is a dispatch loop (parser, interpreter,
    protocol handler, terminal emulator, etc.) runs the extraction pipeline.
    If the pipeline succeeds, it produces this certificate: an extracted model,
    a predicate basis, and a proof that the basis is pullback-closed (SemClosed).

    The pullback closure property is the mathematical core:
    - Ranzato & Tapparo 2004: forward completeness = strong preservation
    - Graf & Saidi 1997: closure under weakest precondition = exact abstraction
    - HMR05: STS1 = finite pre+Boolean closure

    The quotient induced by the basis has at most 2^|basis| states and is
    bisimilar to the concrete system. -/
structure DispatchStructureCertificate
    {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
    (oracle : BranchOracle Sub PC State) where
  /-- The extracted branch model -/
  model : Finset (Branch Sub PC)
  /-- The predicate basis (pullback-closed PC set) -/
  basis : Finset PC
  /-- All branch PCs are in the basis -/
  branch_pcs_in_basis : ∀ b ∈ model, b.pc ∈ basis
  /-- Pullback closure: the basis is semantically closed under lifting
      through model substitutions. This IS SemClosed — the basis predicates
      are closed under preimage through the model's transition functions. -/
  pullback_closed : SemClosed oracle.isa model basis
  /-- The model is a subset of the oracle's target -/
  model_bounded : oracle.TargetBounded model
  /-- The oracle is productive for this model -/
  model_productive : oracle.Productive model
  /-- The model is behaviorally complete -/
  model_complete : BranchModel.Complete oracle.isa
    (↑model : Set (Branch Sub PC)) oracle.behavior

/-- A dispatch structure certificate yields a finite quotient bisimulation.

    This is the soundness theorem: if the pipeline successfully produces
    a certificate, the extracted quotient is bisimilar to the concrete system
    with at most 2^|basis| states.

    The proof is a direct application of quotientBisimulationSem from
    SymExec/Refinement.lean — the certificate bundles exactly the hypotheses
    that theorem requires. -/
theorem dispatch_bisimulation
    {Sub PC State : Type*} [DecidableEq Sub] [DecidableEq PC]
    {oracle : BranchOracle Sub PC State}
    [h_dec : ∀ (s : State) (φ : PC), Decidable (oracle.isa.satisfies s φ)]
    (cert : DispatchStructureCertificate oracle) :
    ∃ n, n ≤ cert.model.card ∧
      CrossBisimulation
        (Quotient.mk (pcSetoidWith oracle.isa cert.basis))
        oracle.behavior
        (abstractBehaviorWith oracle.isa (oracleSequence oracle n) cert.basis) ∧
      Fintype.card (Quotient (pcSetoidWith oracle.isa cert.basis)) ≤
        2 ^ cert.basis.card :=
  quotientBisimulationSem oracle cert.model cert.basis
    cert.branch_pcs_in_basis cert.pullback_closed
    cert.model_productive cert.model_bounded cert.model_complete
