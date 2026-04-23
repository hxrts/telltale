import Distributed.Families.Coordination.API

set_option autoImplicit false

/-! # Distributed.Families.Coordination.Profile

Profile constructors for coordination/CALM theorem-pack attachment.
-/

namespace Distributed
namespace Coordination
namespace Profile

universe u v

/-- Build a coordination characterization profile from semantic assumptions and premises. -/
def mk
    {State : Type u} {Update : Type v}
    (model : Model State Update)
    (assumptions : Assumptions model)
    (premises : Premises model) :
    CoordinationProtocol where
  State := State
  Update := Update
  model := model
  assumptions := assumptions
  premises := premises

end Profile
end Coordination
end Distributed
