import FisherInformationInstance.RealConcrete

/-! # Fisher Information Models

Concrete model exports for `FisherInformationAPI`.
-/

/-
The Problem. Downstream users should be able to select concrete Fisher
information models without depending on implementation internals.

Solution Structure.
1. Import the abstract API boundary.
2. Re-export concrete model definitions as they are introduced.
-/

set_option autoImplicit false

namespace FisherInformationAPI

/-! ## Exported Concrete Models -/

/-- Canonical checked finite-discrete model currently exposed by the instance layer. -/
def finiteDiscreteModel : Model :=
  RealConcrete.unitModel

/-- Canonical checked finite-discrete laws witness currently exposed by the instance layer. -/
def finiteDiscreteLaws : Laws :=
  RealConcrete.unitLaws

end FisherInformationAPI
