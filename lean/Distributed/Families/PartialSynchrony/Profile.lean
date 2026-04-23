import Distributed.Families.PartialSynchrony.API

set_option autoImplicit false

/-! # Distributed.Families.PartialSynchrony.Profile

Profile constructors for partial-synchrony theorem-pack attachment.
-/

namespace Distributed
namespace PartialSynchrony
namespace Profile

universe u v w x

/-- Build a partial-synchrony liveness profile from semantic timed-run assumptions. -/
def mk
    {State : Type u} {Value : Type v} {Event : Type w} {Party : Type x}
    (model : Model State Value Event Party)
    (assumptions : Assumptions model)
    :
    LivenessProtocol where
  State := State
  Value := Value
  Event := Event
  Party := Party
  model := model
  assumptions := assumptions

end Profile
end PartialSynchrony
end Distributed
