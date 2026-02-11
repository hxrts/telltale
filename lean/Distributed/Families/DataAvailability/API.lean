import Distributed.Families.DataAvailability.Core

set_option autoImplicit false

/-! # Distributed.Families.DataAvailability.API

High-level API for automatic DA/retrievability certification.
-/

namespace Distributed
namespace DataAvailability

universe u v

/-- Certified protocol package for DA/retrievability guarantees. -/
structure DAProtocol where
  State : Type u
  Chunk : Type v
  model : Model State Chunk
  assumptions : Assumptions model
  premises : Premises model
  availability :
    DataAvailability model :=
      availability_of_assumptions assumptions premises
  retrievability :
    DataRetrievability model :=
      retrievability_of_assumptions assumptions premises

/-- Extract data-availability theorem from a certified protocol bundle. -/
theorem availability_of_protocol (P : DAProtocol) :
    DataAvailability P.model :=
  P.availability

/-- Extract data-retrievability theorem from a certified protocol bundle. -/
theorem retrievability_of_protocol (P : DAProtocol) :
    DataRetrievability P.model :=
  P.retrievability

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : DAProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end DataAvailability
end Distributed
