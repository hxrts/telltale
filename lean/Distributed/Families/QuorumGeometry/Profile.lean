import Distributed.Families.QuorumGeometry.API

set_option autoImplicit false

/-! # Distributed.Families.QuorumGeometry.Profile

Profile constructors for quorum-geometry theorem-pack attachment.
-/

namespace Distributed
namespace QuorumGeometry
namespace Profile

universe u v w x

/-- Build a quorum-geometry safety profile from semantic assumptions. -/
def mk
    {State : Type u} {Decision : Type v} {Certificate : Type w} {Party : Type x}
    (model : Model State Decision Certificate Party)
    (assumptions : Assumptions model) :
    SafetyProtocol where
  State := State
  Decision := Decision
  Certificate := Certificate
  Party := Party
  model := model
  assumptions := assumptions

end Profile
end QuorumGeometry
end Distributed
