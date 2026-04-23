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

/-- Extract no-split-brain theorem from a certified protocol bundle. -/
theorem no_split_brain_of_protocol (P : ReconfigurationProtocol) :
    NoSplitBrainAcrossReconfiguration P.model :=
  no_split_brain_of_assumptions P.assumptions

/-- Extract safe-handoff theorem from a certified protocol bundle. -/
theorem safe_handoff_of_protocol (P : ReconfigurationProtocol) :
    SafeHandoff P.model :=
  safe_handoff_of_assumptions P.assumptions

/-- Extract liveness-preserved theorem from a certified protocol bundle. -/
theorem liveness_preserved_of_protocol (P : ReconfigurationProtocol) :
    LivenessPreserved P.model :=
  liveness_preserved_of_assumptions P.assumptions

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : ReconfigurationProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end Reconfiguration
end Distributed
