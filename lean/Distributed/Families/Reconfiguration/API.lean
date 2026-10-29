import Distributed.Families.Reconfiguration.Core

set_option autoImplicit false

/-! # Distributed.Families.Reconfiguration.API

High-level API for reconfiguration certification over the joint-consensus model.
-/

namespace Distributed
namespace Reconfiguration

universe v w x

/-- Certified protocol package for reconfiguration guarantees. -/
structure ReconfigurationProtocol where
  Decision : Type v
  Certificate : Type w
  Party : Type x
  [decEq : DecidableEq Party]
  model : Model Decision Certificate Party
  assumptions : Assumptions model

attribute [instance] ReconfigurationProtocol.decEq

/-- No split brain for a certified protocol bundle. -/
theorem no_split_brain_of_protocol (P : ReconfigurationProtocol) :
    NoSplitBrainAcrossReconfiguration P.model :=
  no_split_brain_of_assumptions P.assumptions

/-- Safe handoff for a certified protocol bundle. -/
theorem safe_handoff_of_protocol (P : ReconfigurationProtocol) :
    SafeHandoff P.model :=
  safe_handoff P.model

/-- Liveness preservation for a certified protocol bundle. -/
theorem liveness_preserved_of_protocol (P : ReconfigurationProtocol) :
    LivenessPreserved P.model P.assumptions.byzantine :=
  liveness_preserved_of_assumptions P.assumptions

end Reconfiguration
end Distributed
