import Runtime.VM.Model.EffectsLemmas

set_option autoImplicit false

/-! # Runtime.Proofs.VM.EffectContracts

Proof-facing surface for effect admissibility, totality, and reentrancy
contracts. This keeps the architectural legality rules discoverable under the
runtime proof namespace rather than only inside executable metadata.
-/

namespace Runtime
namespace Proofs
namespace VM

abbrev EffectSemanticClass := Runtime.VM.Model.EffectSemanticClass
abbrev EffectRetryShape := Runtime.VM.Model.EffectRetryShape
abbrev EffectResponsibilityDomain := Runtime.VM.Model.EffectResponsibilityDomain
abbrev architecturallyLegal := Runtime.VM.Model.EffectInterfaceMetadata.architecturallyLegal
abbrev reentrancyAdmissible := Runtime.VM.Model.EffectInterfaceMetadata.reentrancyAdmissible
abbrev observational_surfaces_do_not_author_truth :=
  Runtime.VM.Model.observational_surfaces_do_not_author_truth
abbrev bestEffort_surfaces_do_not_author_truth :=
  Runtime.VM.Model.bestEffort_surfaces_do_not_author_truth
abbrev mayBlock_requires_timeout :=
  Runtime.VM.Model.mayBlock_requires_timeout
abbrev retry_requires_timeout :=
  Runtime.VM.Model.retry_requires_timeout
abbrev internalOnly_requires_internal_handler :=
  Runtime.VM.Model.internalOnly_requires_internal_handler
abbrev same_footprint_nonreentrant :=
  Runtime.VM.Model.same_footprint_nonreentrant
abbrev same_operation_nonreentrant :=
  Runtime.VM.Model.same_operation_nonreentrant
abbrev explicit_same_footprint_reentrancy_admissible :=
  Runtime.VM.Model.explicit_same_footprint_reentrancy_admissible

end VM
end Proofs
end Runtime
