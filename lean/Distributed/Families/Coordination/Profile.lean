import Distributed.Families.Coordination.API

set_option autoImplicit false

/-! # Distributed.Families.Coordination.Profile

Profile constructors for coordination theorem-pack attachment.
-/

namespace Distributed
namespace Coordination
namespace Profile

universe u v

/-- Build a coordination characterization profile from a query model. -/
def mk {Input : Type u} {Output : Type v} [DecidableEq Input]
    (model : Model Input Output) : CoordinationProtocol where
  Input := Input
  Output := Output
  model := model

end Profile
end Coordination
end Distributed
