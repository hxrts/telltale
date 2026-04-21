import Distributed.Families.Nakamoto.API

set_option autoImplicit false

/-! # Distributed.Families.Nakamoto.Profile

Profile constructors for Nakamoto theorem-pack attachment.
-/

namespace Distributed
namespace Nakamoto
namespace Profile

universe u v w

/-- Build a Nakamoto security profile from chain and probability assumptions. -/
def mk
    {State : Type u} {Block : Type v} {Party : Type w}
    (model : Model State Block Party)
    (assumptions : Assumptions model)
    :
    SecurityProtocol where
  State := State
  Block := Block
  Party := Party
  model := model
  assumptions := assumptions

end Profile
end Nakamoto
end Distributed
