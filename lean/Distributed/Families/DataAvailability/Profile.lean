import Distributed.Families.DataAvailability.API

set_option autoImplicit false

/-! # Distributed.Families.DataAvailability.Profile

Profile constructors for data-availability theorem-pack attachment.
-/

namespace Distributed
namespace DataAvailability
namespace Profile

universe u v

/-- Build a data-availability profile from shard and reconstruction assumptions. -/
def mk
    {State : Type u} {Chunk : Type v}
    (model : Model State Chunk)
    (assumptions : Assumptions model)
    :
    DAProtocol where
  State := State
  Chunk := Chunk
  model := model
  assumptions := assumptions

end Profile
end DataAvailability
end Distributed
