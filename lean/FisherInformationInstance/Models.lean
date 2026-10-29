import FisherInformationInstance.RealConcrete
import FisherInformationInstance.BernoulliLaws

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

/-- Canonical checked finite-discrete model: the Bernoulli family (`d = 1`). -/
noncomputable def finiteDiscreteModel : Model :=
  Fixtures.bernoulliModel

/-- Canonical checked finite-discrete laws witness: the Bernoulli laws instance. -/
noncomputable def finiteDiscreteLaws : Laws :=
  RealConcrete.bernoulliLaws

end FisherInformationAPI
