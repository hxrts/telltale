import Distributed.Families.FailureDetectors.API

set_option autoImplicit false

/-! # Distributed.Families.FailureDetectors.Profile

Profile constructors for failure-detector theorem-pack attachment.
-/

namespace Distributed
namespace FailureDetectors
namespace Profile

universe u v

/-- Build a failure-detector boundary profile from semantic assumptions. -/
def mk
    {State : Type u} {Party : Type v}
    (model : Model State Party)
    (assumptions : Assumptions model)
    (detector : DetectorClass) :
    BoundaryProtocol where
  State := State
  Party := Party
  model := model
  assumptions := assumptions
  detector := detector

end Profile
end FailureDetectors
end Distributed
