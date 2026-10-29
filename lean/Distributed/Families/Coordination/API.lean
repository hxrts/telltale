import Distributed.Families.Coordination.Core

set_option autoImplicit false

/-! # Distributed.Families.Coordination.API

High-level API for the coordination (CALM) characterization.
-/

namespace Distributed
namespace Coordination

universe u v

/-- Protocol package for coordination characterization. No assumptions are
needed: the characterization is proved for every query model. -/
structure CoordinationProtocol where
  Input : Type u
  Output : Type v
  [decEq : DecidableEq Input]
  model : Model Input Output

attribute [instance] CoordinationProtocol.decEq

/-- Coordination characterization for a protocol bundle. -/
theorem characterization_of_protocol (P : CoordinationProtocol) :
    CoordinationCharacterization P.model :=
  coordination_characterization P.model

end Coordination
end Distributed
