import Runtime.ProtocolMachine.Model.EffectAlgebra
import Runtime.Proofs.ProtocolMachine.SemanticObjects.ProgressContracts

set_option autoImplicit false

/-!
# Runtime.Proofs.ProtocolMachine.Effects

The Problem.
The proof layer needs direct theorems over effect admissibility, timeout discipline,
retry rules, reentrancy, and multi-effect composition so architectural legality
is not left to prose.

Solution Structure.
This module proves legality consequences for effect-interface metadata and a
small footprint-based reentrancy calculus over semantic responsibility domains.
-/

namespace Runtime.ProtocolMachine.Model

theorem observational_surfaces_do_not_author_truth
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hObs : metadata.semanticClass = .observational) :
    metadata.authorityClass ≠ .authoritative :=
  hLegal.1 hObs

theorem bestEffort_surfaces_do_not_author_truth
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hBestEffort : metadata.semanticClass = .bestEffort) :
    metadata.authorityClass ≠ .authoritative :=
  hLegal.2.1 hBestEffort

theorem mayBlock_requires_timeout
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hMayBlock : metadata.totality = .mayBlock) :
    metadata.timeoutRequired :=
  hLegal.2.2.1 hMayBlock

theorem retry_requires_timeout
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hRetry : metadata.hasExplicitRetryRule) :
    metadata.timeoutRequired :=
  hLegal.2.2.2.1 hRetry

theorem internalOnly_requires_internal_handler
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hInternalOnly : metadata.admissibility = .internalOnly) :
    metadata.handlerDomain = .internal :=
  hLegal.2.2.2.2 hInternalOnly

theorem rejectSameOperation_blocks_same_operation
    (active incoming : EffectResponsibilityDomain)
    (hSame : active.sameOperation incoming) :
    ¬ EffectReentrancyPolicy.admits .rejectSameOperation active incoming := by
  simpa [EffectReentrancyPolicy.admits] using hSame

theorem rejectSameFragment_blocks_same_footprint
    (active incoming : EffectResponsibilityDomain)
    (hSame : active.sameSemanticFootprint incoming) :
    ¬ EffectReentrancyPolicy.admits .rejectSameFragment active incoming := by
  simpa [EffectReentrancyPolicy.admits] using hSame

theorem same_footprint_nonreentrant
    (metadata : EffectInterfaceMetadata)
    (active incoming : EffectResponsibilityDomain)
    (hLegal : metadata.architecturallyLegal)
    (hPolicy : metadata.reentrancyPolicy = .rejectSameFragment)
    (hSame : active.sameSemanticFootprint incoming) :
    ¬ metadata.reentrancyAdmissible active incoming := by
  intro hAdmissible
  rcases hAdmissible with ⟨_, hReentrant⟩
  have hReject : EffectReentrancyPolicy.admits .rejectSameFragment active incoming := by
    simpa [hPolicy] using hReentrant
  exact rejectSameFragment_blocks_same_footprint active incoming hSame hReject

theorem same_operation_nonreentrant
    (metadata : EffectInterfaceMetadata)
    (active incoming : EffectResponsibilityDomain)
    (hLegal : metadata.architecturallyLegal)
    (hPolicy : metadata.reentrancyPolicy = .rejectSameOperation)
    (hSame : active.sameOperation incoming) :
    ¬ metadata.reentrancyAdmissible active incoming := by
  intro hAdmissible
  rcases hAdmissible with ⟨_, hReentrant⟩
  have hReject : EffectReentrancyPolicy.admits .rejectSameOperation active incoming := by
    simpa [hPolicy] using hReentrant
  exact rejectSameOperation_blocks_same_operation active incoming hSame hReject

theorem explicit_same_footprint_reentrancy_admissible
    (metadata : EffectInterfaceMetadata)
    (active incoming : EffectResponsibilityDomain)
    (hLegal : metadata.architecturallyLegal)
    (hAllow : metadata.reentrancyPolicy = .allow) :
    metadata.reentrancyAdmissible active incoming := by
  refine ⟨hLegal, ?_⟩
  simp [hAllow, EffectReentrancyPolicy.admits]

end Runtime.ProtocolMachine.Model

namespace Runtime.ProtocolMachine.Model

/-! ## Classification -/

theorem authoritative_classification
    (metadata : EffectInterfaceMetadata) :
    metadata.isAuthoritative ↔ metadata.authorityClass = .authoritative :=
  Iff.rfl

theorem command_classification
    (metadata : EffectInterfaceMetadata) :
    metadata.isCommand ↔ metadata.authorityClass = .command :=
  Iff.rfl

theorem observe_classification
    (metadata : EffectInterfaceMetadata) :
    metadata.isObserve ↔ metadata.authorityClass = .observe :=
  Iff.rfl

theorem observational_effects_cannot_discharge_authoritative_obligations
    (metadata : EffectInterfaceMetadata)
    (hLegal : metadata.architecturallyLegal)
    (hObs : metadata.semanticClass = .observational) :
    ¬ metadata.isAuthoritative := by
  intro hAuthoritative
  exact observational_surfaces_do_not_author_truth metadata hLegal hObs hAuthoritative

/-! ## Immediate Effects -/

theorem immediate_admissible_requires_mustTerminate
    (metadata : EffectInterfaceMetadata)
    (hImmediate : metadata.immediateAdmissible) :
    metadata.totality = .mustTerminate :=
  hImmediate.2.1.1

theorem immediate_admissible_forbids_timeout
    (metadata : EffectInterfaceMetadata)
    (hImmediate : metadata.immediateAdmissible) :
    metadata.timeoutPolicy = .none :=
  hImmediate.2.1.2.1

theorem immediate_admissible_forbids_retry
    (metadata : EffectInterfaceMetadata)
    (hImmediate : metadata.immediateAdmissible) :
    metadata.retryShape = .forbidden :=
  hImmediate.2.1.2.2

theorem immediate_admissible_not_authoritative
    (metadata : EffectInterfaceMetadata)
    (hImmediate : metadata.immediateAdmissible) :
    ¬ metadata.isAuthoritative :=
  hImmediate.2.2

/-! ## Composition Helpers -/

theorem success_outcome_terminal
    (record : EffectExchangeRecord)
    (hSuccess : record.succeeded) :
    record.terminal := by
  cases hStatus : record.outcome.status <;>
    simp [EffectExchangeRecord.succeeded, EffectExchangeRecord.terminal,
      EffectOutcomeStatus.isSuccess, EffectOutcomeStatus.isTerminal, hStatus] at hSuccess ⊢

/-! ## Composition Policies -/

theorem allSuccess_resolves_commitment
    (records : List EffectExchangeRecord)
    (hNonEmpty : records ≠ [])
    (hAll : ∀ record ∈ records, record.succeeded) :
    EffectCompositionPolicy.commitmentResolved .allSuccess records :=
  ⟨hNonEmpty, hAll⟩

theorem firstSuccess_resolves_commitment
    (records : List EffectExchangeRecord)
    {record : EffectExchangeRecord}
    (hMem : record ∈ records)
    (hSuccess : record.succeeded) :
    EffectCompositionPolicy.commitmentResolved .firstSuccess records :=
  ⟨record, hMem, hSuccess⟩

theorem quorum_resolves_commitment
    (records : List EffectExchangeRecord)
    (requiredSuccesses : Nat)
    (hPositive : requiredSuccesses > 0)
    (hEnough : countSuccessfulEffects records ≥ requiredSuccesses) :
    EffectCompositionPolicy.commitmentResolved (.quorum requiredSuccesses) records :=
  ⟨hPositive, hEnough⟩

theorem fallback_resolves_commitment_of_success
    (records : List EffectExchangeRecord)
    {record : EffectExchangeRecord}
    (hMem : record ∈ records)
    (hSuccess : record.succeeded) :
    EffectCompositionPolicy.commitmentResolved .fallback records :=
  Or.inl ⟨record, hMem, hSuccess⟩

theorem fallback_resolves_commitment_of_terminal_failover
    (records : List EffectExchangeRecord)
    (hNonEmpty : records ≠ [])
    (hTerminal : ∀ record ∈ records, record.terminal) :
    EffectCompositionPolicy.commitmentResolved .fallback records :=
  Or.inr ⟨hNonEmpty, hTerminal⟩

/-! ## Commitment / Progress Links -/

theorem allSuccess_commitment_compatible
    (records : List EffectExchangeRecord) :
    EffectCompositionPolicy.commitmentCompatible .allSuccess records := by
  intro hResolved record hMem
  exact hResolved.2 record hMem

theorem firstSuccess_commitment_compatible
    (records : List EffectExchangeRecord) :
    EffectCompositionPolicy.commitmentCompatible .firstSuccess records := by
  intro hResolved
  exact hResolved

theorem quorum_commitment_compatible
    (records : List EffectExchangeRecord)
    (requiredSuccesses : Nat) :
    EffectCompositionPolicy.commitmentCompatible (.quorum requiredSuccesses) records := by
  intro hResolved
  exact hResolved.2

theorem fallback_commitment_compatible
    (records : List EffectExchangeRecord) :
    EffectCompositionPolicy.commitmentCompatible .fallback records := by
  intro hResolved
  exact hResolved

theorem composition_progress_of_schedulingBoundCompatible
    (policy : EffectCompositionPolicy)
    (records : List EffectExchangeRecord)
    (contract : ProgressContract)
    (hBound : contract.schedulingBoundCompatible) :
    policy.progressCompatible records contract := by
  intro _hResolved
  by_cases hTerminal : contract.isTerminal
  · exact Or.inl hTerminal
  · rcases hBound hTerminal with ⟨next, hStep, hDecrease⟩
    exact Or.inr ⟨next, hStep, hDecrease⟩

end Runtime.ProtocolMachine.Model
