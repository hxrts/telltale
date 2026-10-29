import Distributed.Families.CAP.API

set_option autoImplicit false

/-! # Distributed.Families.CAP.Profile

Profile constructors for CAP theorem-pack attachment.
-/

namespace Distributed
namespace CAP
namespace Profile

/-- Build a CAP impossibility profile from a register algorithm and two
distinct register values. -/
def mk {Val Msg St : Type} (algorithm : Register.Algorithm Val Msg St)
    (v₀ v₁ : Val) (h : v₁ ≠ v₀) : ImpossibilityProtocol where
  Val := Val
  Msg := Msg
  St := St
  algorithm := algorithm
  initialValue := v₀
  otherValue := v₁
  distinct := h

end Profile
end CAP
end Distributed
