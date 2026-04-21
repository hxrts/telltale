import Distributed.Families.TriangleOfForgetting.API

set_option autoImplicit false

/-! # Distributed.Families.TriangleOfForgetting.Profile

Profile constructors for triangle-of-forgetting theorem-pack attachment.
-/

namespace Distributed
namespace TriangleOfForgetting
namespace Profile

universe u v w x

/-- Build a triangle-of-forgetting impossibility profile from semantic assumptions. -/
def mk
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (model : Model State Update Member View)
    (assumptions : Assumptions model) :
    ImpossibilityProtocol where
  State := State
  Update := Update
  Member := Member
  View := View
  model := model
  assumptions := assumptions

end Profile
end TriangleOfForgetting
end Distributed
