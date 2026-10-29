import Distributed.Families.CAP.Core
import Distributed.Families.CAP.Theorem

set_option autoImplicit false

/-! # Distributed.Families.CAP.API

High-level API for the CAP impossibility (Gilbert–Lynch 2002).

A bundle supplies a concrete two-node register algorithm and two distinct
register values; the CAP theorem (not available-under-partition and atomic at
once) is derived from `Register.cap_impossible`.
-/

namespace Distributed
namespace CAP

/-- A register algorithm packaged for CAP certification. -/
structure ImpossibilityProtocol where
  Val : Type
  Msg : Type
  St : Type
  algorithm : Register.Algorithm Val Msg St
  initialValue : Val
  otherValue : Val
  distinct : otherValue ≠ initialValue

/-- The CAP guarantee for a bundle: availability under partition plus atomicity. -/
def CAPGuarantee (P : ImpossibilityProtocol) : Prop :=
  Register.Available P.algorithm ∧ Register.Atomic P.algorithm P.initialValue

/-- CAP impossibility for a certified bundle. -/
theorem impossibility_of_protocol (P : ImpossibilityProtocol) : ¬ CAPGuarantee P :=
  Register.cap_impossible P.algorithm P.initialValue P.otherValue P.distinct

/-- Corollary: an available algorithm is not atomic. -/
theorem consistency_impossible_with_availability (P : ImpossibilityProtocol)
    (hAvail : Register.Available P.algorithm) :
    ¬ Register.Atomic P.algorithm P.initialValue :=
  fun hAt => impossibility_of_protocol P ⟨hAvail, hAt⟩

end CAP
end Distributed
