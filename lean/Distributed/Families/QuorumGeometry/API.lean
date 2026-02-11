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
  noConflictingCommits :
    ∀ {s d₁ d₂},
      Committed model s d₁ →
      Committed model s d₂ →
      ¬ model.conflicts d₁ d₂ := by
        intro s d₁ d₂ hCommitted₁ hCommitted₂
        exact no_conflicting_commits_of_assumptions assumptions hCommitted₁ hCommitted₂
  forkExclusion :
    ∀ s, ¬ Forked model s := by
      intro s
      exact fork_exclusion_of_assumptions assumptions s
  safeFinality :
    ∀ {s d},
      Finalized model s d →
      ∀ d', Committed model s d' → ¬ model.conflicts d d' := by
        intro s d hFinalized d' hCommitted
        exact safe_finality_of_assumptions assumptions hFinalized d' hCommitted

/-- Extract no-conflicting-commits theorem from a certified protocol bundle. -/
theorem noConflictingCommits_of_protocol (P : SafetyProtocol) :
    ∀ {s d₁ d₂},
      Committed P.model s d₁ →
      Committed P.model s d₂ →
      ¬ P.model.conflicts d₁ d₂ :=
  P.noConflictingCommits

/-- Extract fork-exclusion theorem from a certified protocol bundle. -/
theorem forkExclusion_of_protocol (P : SafetyProtocol) :
    ∀ s, ¬ Forked P.model s :=
  P.forkExclusion

/-- Extract safe-finality theorem from a certified protocol bundle. -/
theorem safeFinality_of_protocol (P : SafetyProtocol) :
    ∀ {s d},
      Finalized P.model s d →
      ∀ d', Committed P.model s d' → ¬ P.model.conflicts d d' :=
  P.safeFinality

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : SafetyProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end QuorumGeometry
end Distributed
