import Distributed.Families.Reconfiguration.API

set_option autoImplicit false

/-! # Distributed.Families.Reconfiguration.Profile

Profile constructors for reconfiguration theorem-pack attachment.
-/

namespace Distributed
namespace Reconfiguration
namespace Profile

universe v w x

/-- Build a reconfiguration profile from a model and its fault-model assumptions. -/
def mk
    {Decision : Type v} {Certificate : Type w} {Party : Type x} [DecidableEq Party]
    (model : Model Decision Certificate Party)
    (assumptions : Assumptions model) :
    ReconfigurationProtocol where
  Decision := Decision
  Certificate := Certificate
  Party := Party
  model := model
  assumptions := assumptions

end Profile
end Reconfiguration
end Distributed
