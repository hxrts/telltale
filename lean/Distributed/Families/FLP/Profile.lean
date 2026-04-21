import Distributed.Families.FLP.API

set_option autoImplicit false

/-! # Distributed.Families.FLP.Profile

Profile constructors for FLP theorem-pack attachment.
-/

namespace Distributed
namespace FLP
namespace Profile

universe u v w x

/-- Build an FLP lower-bound profile from semantic assumptions and premises. -/
def mkLowerBound
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (model : Model State Value Event Party)
    (assumptions : Assumptions model)
    (premises : LowerBoundPremises model) :
    LowerBoundProtocol where
  State := State
  Value := Value
  Event := Event
  Party := Party
  model := model
  assumptions := assumptions
  premises := premises

/-- Build an FLP impossibility profile from semantic assumptions and premises. -/
def mkImpossibility
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (model : Model State Value Event Party)
    (assumptions : Assumptions model)
    (premises : ImpossibilityPremises model) :
    ImpossibilityProtocol where
  State := State
  Value := Value
  Event := Event
  Party := Party
  model := model
  assumptions := assumptions
  premises := premises

end Profile
end FLP
end Distributed
