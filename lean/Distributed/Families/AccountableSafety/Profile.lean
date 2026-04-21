import Distributed.Families.AccountableSafety.API

set_option autoImplicit false

/-! # Distributed.Families.AccountableSafety.Profile

Profile constructors for accountable-safety theorem-pack attachment.
-/

namespace Distributed
namespace AccountableSafety
namespace Profile

universe u v w

/-- Build an accountable-safety profile from conflict-evidence assumptions. -/
def mk
    {State : Type u} {Decision : Type v} {Fault : Type w}
    (model : Model State Decision Fault)
    (assumptions : Assumptions model)
    :
    AccountableProtocol where
  State := State
  Decision := Decision
  Fault := Fault
  model := model
  assumptions := assumptions

end Profile
end AccountableSafety
end Distributed
