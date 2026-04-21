import Distributed.Families.Responsiveness.API

set_option autoImplicit false

/-! # Distributed.Families.Responsiveness.Profile

Profile constructors for responsiveness theorem-pack attachment.
-/

namespace Distributed
namespace Responsiveness
namespace Profile

universe u v w x

/-- Build a responsiveness profile from semantic optimistic-run assumptions. -/
def mk
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (model : Model State Value Event Party)
    (assumptions : Assumptions model)
    :
    ResponsiveProtocol where
  State := State
  Value := Value
  Event := Event
  Party := Party
  model := model
  assumptions := assumptions

end Profile
end Responsiveness
end Distributed
