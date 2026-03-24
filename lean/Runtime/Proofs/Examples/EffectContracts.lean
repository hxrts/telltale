import Runtime.VM.Model

set_option autoImplicit false

/-! # Runtime.Proofs.Examples.EffectContracts

Small example witnesses for effect admissibility, totality, and reentrancy
contracts.
-/

namespace Runtime
namespace Proofs
namespace Examples

open Runtime.VM.Model

def boundedAuthoritativeEffect : EffectInterfaceMetadata :=
  { interfaceName := "storage"
  , operationName := "commit"
  , authorityClass := .authoritative
  , semanticClass := .authoritative
  , admissibility := .declaredUseOnly
  , totality := .mayBlock
  , timeoutPolicy := .required (some 5)
  , retryShape := .bounded 2
  , reentrancyPolicy := .rejectSameFragment
  , handlerDomain := .external
  }

def reentrantObservationEffect : EffectInterfaceMetadata :=
  { interfaceName := "audit"
  , operationName := "emit"
  , authorityClass := .observe
  , semanticClass := .observational
  , admissibility := .always
  , totality := .mustTerminate
  , timeoutPolicy := .none
  , retryShape := .forbidden
  , reentrancyPolicy := .allow
  , handlerDomain := .external
  }

def sameFootprintDomain : EffectResponsibilityDomain :=
  { footprintKey := "session:core"
  , operationId := some "op-1"
  , fragmentId := some "fragment-a"
  , ownerId := some "owner-a"
  }

def sameFootprintDomain' : EffectResponsibilityDomain :=
  { footprintKey := "session:core"
  , operationId := some "op-2"
  , fragmentId := some "fragment-b"
  , ownerId := some "owner-b"
  }

theorem boundedAuthoritativeEffect_legal :
    boundedAuthoritativeEffect.architecturallyLegal := by
  constructor
  · intro hObs
    cases hObs
  constructor
  · intro hBestEffort
    cases hBestEffort
  constructor
  · intro _
    simp [EffectInterfaceMetadata.timeoutRequired,
      EffectTimeoutPolicy.requiresExplicitTimeout, boundedAuthoritativeEffect]
  constructor
  · intro _
    simp [EffectInterfaceMetadata.timeoutRequired,
      EffectTimeoutPolicy.requiresExplicitTimeout, boundedAuthoritativeEffect]
  · intro hInternalOnly
    cases hInternalOnly

theorem reentrantObservationEffect_legal :
    reentrantObservationEffect.architecturallyLegal := by
  constructor
  · intro _
    intro hAuthoritative
    cases hAuthoritative
  constructor
  · intro hBestEffort
    cases hBestEffort
  constructor
  · intro hMayBlock
    cases hMayBlock
  constructor
  · intro hRetry
    cases hRetry
  · intro hInternalOnly
    cases hInternalOnly

example : boundedAuthoritativeEffect.architecturallyLegal := by
  exact boundedAuthoritativeEffect_legal

example :
    ¬ boundedAuthoritativeEffect.reentrancyAdmissible
      sameFootprintDomain sameFootprintDomain' := by
  apply Runtime.VM.Model.same_footprint_nonreentrant
  · exact boundedAuthoritativeEffect_legal
  · rfl
  · rfl

example :
    reentrantObservationEffect.reentrancyAdmissible
      sameFootprintDomain sameFootprintDomain' := by
  apply Runtime.VM.Model.explicit_same_footprint_reentrancy_admissible
  · exact reentrantObservationEffect_legal
  · rfl

end Examples
end Proofs
end Runtime
