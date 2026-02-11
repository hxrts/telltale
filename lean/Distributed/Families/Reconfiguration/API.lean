import Distributed.Families.Reconfiguration.Core

set_option autoImplicit false

/-! # Distributed.Families.Reconfiguration.API

High-level API for automatic reconfiguration certification.
-/

namespace Distributed
namespace Reconfiguration

universe u v w

/-- Certified protocol package for reconfiguration guarantees. -/
structure ReconfigurationProtocol where
  State : Type u
  Decision : Type v
  Certificate : Type w
  model : Model State Decision Certificate
  assumptions : Assumptions model
  premises : Premises model
  noSplitBrain :
    NoSplitBrainAcrossReconfiguration model :=
      no_split_brain_of_assumptions assumptions premises
  safeHandoff :
    SafeHandoff model :=
      safe_handoff_of_assumptions assumptions premises
  livenessPreserved :
    LivenessPreserved model :=
      liveness_preserved_of_assumptions assumptions premises

/-- Extract no-split-brain theorem from a certified protocol bundle. -/
theorem noSplitBrain_of_protocol (P : ReconfigurationProtocol) :
    NoSplitBrainAcrossReconfiguration P.model :=
  P.noSplitBrain

/-- Extract safe-handoff theorem from a certified protocol bundle. -/
theorem safeHandoff_of_protocol (P : ReconfigurationProtocol) :
    SafeHandoff P.model :=
  P.safeHandoff

/-- Extract liveness-preserved theorem from a certified protocol bundle. -/
theorem livenessPreserved_of_protocol (P : ReconfigurationProtocol) :
    LivenessPreserved P.model :=
  P.livenessPreserved

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : ReconfigurationProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Reconfiguration
end Distributed
