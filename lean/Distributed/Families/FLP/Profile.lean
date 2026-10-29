import Distributed.Families.FLP.API

set_option autoImplicit false

/-! # Distributed.Families.FLP.Profile

Profile constructors for FLP theorem-pack attachment.
-/

namespace Distributed
namespace FLP
namespace Profile

/-- Build an FLP impossibility profile from a concrete protocol and its
agreement and validity proofs. -/
def mkImpossibility {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]
    [Fintype Proc] [Countable Msg] (protocol : Async.Protocol Proc Msg St)
    (twoProcs : ∃ p q : Proc, p ≠ q) (agreement : Async.Agreement protocol)
    (validity : Async.Validity protocol) : ImpossibilityProtocol where
  Proc := Proc
  Msg := Msg
  St := St
  protocol := protocol
  twoProcs := twoProcs
  agreement := agreement
  validity := validity

end Profile
end FLP
end Distributed
