import Distributed.Families.DataAvailability.API

set_option autoImplicit false

/-! # Distributed.Families.DataAvailability.Profile

Profile constructors for DA theorem-pack attachment.
-/

namespace Distributed
namespace DataAvailability
namespace Profile

universe u v

/-- Build a DA profile from an erasure-coding model and its assumptions. -/
def mk {F : Type u} [Field F] {Party : Type v} [DecidableEq Party]
    (model : Model F Party) (assumptions : Assumptions model) : DAProtocol where
  Field := F
  Party := Party
  model := model
  assumptions := assumptions

end Profile
end DataAvailability
end Distributed
