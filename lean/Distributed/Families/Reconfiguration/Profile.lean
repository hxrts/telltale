import Distributed.Families.Reconfiguration.API

set_option autoImplicit false

/-! # Distributed.Families.Reconfiguration.Profile

Profile constructors for reconfiguration theorem-pack attachment.
-/

namespace Distributed
namespace Reconfiguration
namespace Profile

universe u v w

/-- Build a reconfiguration profile from semantic reconfiguration assumptions. -/
def mk
    {State : Type u} {Decision : Type v} {Certificate : Type w}
    (model : Model State Decision Certificate)
    (assumptions : Assumptions model) :
    ReconfigurationProtocol where
  State := State
  Decision := Decision
  Certificate := Certificate
  model := model
  assumptions := assumptions

end Profile
end Reconfiguration
end Distributed
