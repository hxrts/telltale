import Runtime.ProtocolMachine.Model.Effects

set_option autoImplicit false

/-!
# Runtime.ProtocolMachine.Model.EffectsLemmas

The Problem.
Effect admissibility, timeout discipline, retry rules, and reentrancy were
previously carried only as metadata. The proof layer needs direct theorems over
that metadata so architectural legality is not left to prose.

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
