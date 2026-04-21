import Distributed.Families.QuorumGeometry.Core

set_option autoImplicit false

/-! # Distributed.Families.QuorumGeometry.API

High-level API for automatic quorum-geometry safety certification.
-/

namespace Distributed
namespace QuorumGeometry

universe u v w x

/-- Certified protocol package for quorum-geometry safety properties. -/
structure SafetyProtocol where
  State : Type u
  Decision : Type v
  Certificate : Type w
  Party : Type x
  model : Model State Decision Certificate Party
  assumptions : Assumptions model

/-- Extract no-conflicting-commits theorem from a certified protocol bundle. -/
theorem no_conflicting_commits_of_protocol (P : SafetyProtocol) :
    ∀ {s d₁ d₂},
      Committed P.model s d₁ →
      Committed P.model s d₂ →
      ¬ P.model.conflicts d₁ d₂ :=
  fun hCommitted₁ hCommitted₂ =>
    no_conflicting_commits_of_assumptions P.assumptions hCommitted₁ hCommitted₂

/-- Extract fork-exclusion theorem from a certified protocol bundle. -/
theorem fork_exclusion_of_protocol (P : SafetyProtocol) :
    ∀ s, ¬ Forked P.model s :=
  fork_exclusion_of_assumptions P.assumptions

/-- Extract safe-finality theorem from a certified protocol bundle. -/
theorem safe_finality_of_protocol (P : SafetyProtocol) :
    ∀ {s d},
      Finalized P.model s d →
      ∀ d', Committed P.model s d' → ¬ P.model.conflicts d d' :=
  fun hFinalized d' hCommitted =>
    safe_finality_of_assumptions P.assumptions hFinalized d' hCommitted

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : SafetyProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end QuorumGeometry
end Distributed
