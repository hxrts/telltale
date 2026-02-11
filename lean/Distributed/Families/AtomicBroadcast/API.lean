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
  premises : Premises model
  totalOrderConsistency :
    TotalOrderConsistency model :=
      total_order_consistency_of_assumptions assumptions premises
  logPrefixCompatibility :
    LogPrefixCompatibility model :=
      log_prefix_compatibility_of_assumptions assumptions premises
  consensusAtomicBroadcastBridge :
    ConsensusAtomicBroadcastBridge model :=
      bridge_of_assumptions assumptions premises

/-- Extract total-order-consistency theorem from a certified protocol bundle. -/
theorem totalOrderConsistency_of_protocol (P : AtomicBroadcastProtocol) :
    TotalOrderConsistency P.model :=
  P.totalOrderConsistency

/-- Extract log-prefix-compatibility theorem from a certified protocol bundle. -/
theorem logPrefixCompatibility_of_protocol (P : AtomicBroadcastProtocol) :
    LogPrefixCompatibility P.model :=
  P.logPrefixCompatibility

/-- Extract consensus/AB bridge theorem from a certified protocol bundle. -/
theorem bridge_of_protocol (P : AtomicBroadcastProtocol) :
    ConsensusAtomicBroadcastBridge P.model :=
  P.consensusAtomicBroadcastBridge

/-- Core assumptions are always validated for a certified protocol. -/
theorem coreAssumptions_allPassed (P : AtomicBroadcastProtocol) :
    (runAssumptionValidation P.assumptions coreAssumptions).allPassed = true := by
  rfl

end AtomicBroadcast
end Distributed
