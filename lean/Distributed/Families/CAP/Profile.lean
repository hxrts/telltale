import Distributed.Families.CAP.API

set_option autoImplicit false

/-! # Distributed.Families.CAP.Profile

Profile constructors for CAP theorem-pack attachment.
-/

namespace Distributed
namespace CAP
namespace Profile

universe u v

/-- Build a CAP impossibility profile from semantic assumptions and premises. -/
def mk
    {State : Type u} {Party : Type v}
    (model : Model State Party)
    (assumptions : Assumptions model)
    (premises : ImpossibilityPremises model) :
    ImpossibilityProtocol where
  State := State
  Party := Party
  model := model
  assumptions := assumptions
  premises := premises

end Profile
end CAP
end Distributed
