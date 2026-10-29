import Distributed.Families.FLP.Core
import Distributed.Families.FLP.Theorem

set_option autoImplicit false

/-! # Distributed.Families.FLP.API

High-level API for the FLP impossibility (Fischer–Lynch–Paterson 1985).

A protocol bundle supplies a concrete asynchronous protocol
(`Async.Protocol`) with at least two processes, together with proofs of
agreement and validity. FLP impossibility (no termination on all admissible
runs with one crash) and the non-deciding admissible run are then *derived*
from `Async.flp_impossibility`; nothing about valency is assumed.
-/

namespace Distributed
namespace FLP

/-- A consensus protocol packaged for FLP certification. -/
structure ImpossibilityProtocol where
  Proc : Type
  Msg : Type
  St : Type
  [decProc : DecidableEq Proc]
  [decMsg : DecidableEq Msg]
  [finProc : Fintype Proc]
  [countMsg : Countable Msg]
  protocol : Async.Protocol Proc Msg St
  twoProcs : ∃ p q : Proc, p ≠ q
  agreement : Async.Agreement protocol
  validity : Async.Validity protocol

attribute [instance] ImpossibilityProtocol.decProc ImpossibilityProtocol.decMsg
  ImpossibilityProtocol.finProc ImpossibilityProtocol.countMsg

/-- The FLP non-termination witness: an admissible run from an initial
configuration in which no process ever decides. -/
def NonDecidingRun (P : ImpossibilityProtocol) : Prop :=
  ∃ r : Async.Run P.protocol, (∃ I, r.cfg 0 = Async.initCfg P.protocol I) ∧
    r.Admissible ∧ ∀ k v, ¬ Async.Decided P.protocol (r.cfg k) v

/-- FLP impossibility for a certified protocol bundle. -/
theorem impossibility_of_protocol (P : ImpossibilityProtocol) :
    ¬ Async.Termination P.protocol :=
  Async.flp_impossibility P.agreement P.validity P.twoProcs

/-- FLP lower bound: a certified protocol has an admissible non-deciding run. -/
theorem lower_bound_of_protocol (P : ImpossibilityProtocol) : NonDecidingRun P :=
  Async.flp_nondeciding_run P.agreement P.validity P.twoProcs

end FLP
end Distributed
