import Distributed.Families.DataAvailability.Core

set_option autoImplicit false

/-! # Distributed.Families.DataAvailability.API

High-level API for erasure-coded data availability certification.
-/

namespace Distributed
namespace DataAvailability

universe u v

/-- Certified protocol package for DA/retrievability guarantees. -/
structure DAProtocol where
  Field : Type u
  [field : _root_.Field Field]
  Party : Type v
  [decEq : DecidableEq Party]
  model : Model Field Party
  assumptions : Assumptions model

attribute [instance] DAProtocol.field DAProtocol.decEq

/-- Data availability for a certified protocol bundle. -/
theorem availability_of_protocol (P : DAProtocol) :
    DataAvailability P.model :=
  availability_of_assumptions P.assumptions

/-- Data retrievability for a certified protocol bundle. -/
theorem retrievability_of_protocol (P : DAProtocol) :
    DataRetrievability P.model :=
  retrievability_of_assumptions P.assumptions

end DataAvailability
end Distributed
