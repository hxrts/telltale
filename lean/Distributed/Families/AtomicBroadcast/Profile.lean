import Distributed.Families.AtomicBroadcast.API

set_option autoImplicit false

/-! # Distributed.Families.AtomicBroadcast.Profile

Profile constructors for atomic-broadcast theorem-pack attachment.
-/

namespace Distributed
namespace AtomicBroadcast
namespace Profile

universe u v w

/-- Build an atomic-broadcast profile from semantic assumptions. -/
def mk
    {State : Type u} {Message : Type v} {Value : Type w}
    (model : Model State Message Value)
    (assumptions : Assumptions model) :
    AtomicBroadcastProtocol where
  State := State
  Message := Message
  Value := Value
  model := model
  assumptions := assumptions

end Profile
end AtomicBroadcast
end Distributed
