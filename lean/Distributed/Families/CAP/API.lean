import Distributed.Families.CAP.Core

set_option autoImplicit false

/-! # Distributed.Families.CAP.API

High-level API for automatic CAP impossibility certification.

When a protocol bundle includes the reusable CAP assumptions and impossibility
premises, the CAP impossibility theorem is derived automatically.
-/

namespace Distributed
namespace CAP

universe u v

/-- Full CAP-certified protocol package.

`impossibility` has a default proof term, so users provide model assumptions
and premises once, then receive the theorem automatically. -/
structure ImpossibilityProtocol where
  State : Type u
  Party : Type v
  model : Model State Party
  assumptions : Assumptions model
  premises : ImpossibilityPremises model
  impossibility :
    ¬ CAPGuarantee model premises.PartitionRun :=
      impossibility_of_assumptions assumptions premises

/-- Extract the full CAP impossibility theorem from a certified protocol bundle. -/
theorem impossibility_of_protocol (P : ImpossibilityProtocol) :
    ¬ CAPGuarantee P.model P.premises.PartitionRun :=
  P.impossibility

/-- FLP-style summary: core CAP assumptions are validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : ImpossibilityProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end CAP
end Distributed
