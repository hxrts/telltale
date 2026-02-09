import Consensus.CAP.Hypotheses

set_option autoImplicit false

/-! # Consensus.CAP.Api

High-level API for automatic CAP impossibility certification.

When a protocol bundle includes the reusable CAP assumptions and impossibility
premises, the CAP impossibility theorem is derived automatically.
-/

namespace Consensus
namespace CAP

universe u v

/-- Full CAP-certified protocol package.

`impossibility` has a default proof term, so users provide model assumptions
and premises once, then receive the theorem automatically. -/
structure FullProtocol where
  State : Type u
  Party : Type v
  model : Model State Party
  assumptions : Assumptions model
  premises : ImpossibilityPremises model
  impossibility :
    ¬ CAPGuarantee model premises.PartitionRun :=
      impossibility_of_hypotheses assumptions premises

/-- Extract the full CAP impossibility theorem from a certified protocol bundle. -/
theorem impossibility_of_protocol (P : FullProtocol) :
    ¬ CAPGuarantee P.model P.premises.PartitionRun :=
  P.impossibility

/-- FLP-style summary: core CAP assumptions are validated for a certified protocol. -/
theorem coreHypotheses_allPassed (P : FullProtocol) :
    (runValidation P.assumptions coreHypotheses).2 = true := by
  rfl

end CAP
end Consensus
