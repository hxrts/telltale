import Distributed.Families.AtomicBroadcast.Core

set_option autoImplicit false

/-! # Distributed.Families.AtomicBroadcast.API

High-level API for automatic atomic-broadcast certification.
-/

namespace Distributed
namespace AtomicBroadcast

universe u v w

/-- Certified protocol package for atomic-broadcast guarantees. -/
structure AtomicBroadcastProtocol where
  State : Type u
  Message : Type v
  Value : Type w
  model : Model State Message Value
  assumptions : Assumptions model

/-- Extract total-order-consistency theorem from a certified protocol bundle. -/
theorem total_order_consistency_of_protocol (P : AtomicBroadcastProtocol) :
    TotalOrderConsistency P.model :=
  total_order_consistency_of_assumptions P.assumptions

/-- Extract log-prefix-compatibility theorem from a certified protocol bundle. -/
theorem log_prefix_compatibility_of_protocol (P : AtomicBroadcastProtocol) :
    LogPrefixCompatibility P.model :=
  log_prefix_compatibility_of_assumptions P.assumptions

/-- Extract consensus/AB bridge theorem from a certified protocol bundle. -/
theorem bridge_of_protocol (P : AtomicBroadcastProtocol) :
    ConsensusAtomicBroadcastBridge P.model :=
  bridge_of_assumptions P.assumptions

/-- Core assumptions are always validated for a certified protocol. -/
theorem core_assumptions_all_passed (P : AtomicBroadcastProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end AtomicBroadcast
end Distributed
