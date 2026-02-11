import Distributed.Families.AccountableSafety.Core

set_option autoImplicit false

/-! # Distributed.Families.AccountableSafety.API

High-level API for automatic accountable-safety certification.
-/

namespace Distributed
namespace AccountableSafety

universe u v w

/-- Certified protocol package for accountable-safety guarantees. -/
structure AccountableProtocol where
  State : Type u
  Decision : Type v
  Fault : Type w
  model : Model State Decision Fault
  assumptions : Assumptions model
  premises : Premises model
  accountableSafety :
    AccountableSafety model :=
      accountable_safety_of_assumptions assumptions premises

/-- Extract accountable-safety theorem from a certified protocol bundle. -/
theorem accountableSafety_of_protocol (P : AccountableProtocol) :
    AccountableSafety P.model :=
  P.accountableSafety

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : AccountableProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end AccountableSafety
end Distributed
