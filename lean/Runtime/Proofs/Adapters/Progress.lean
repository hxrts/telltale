import Runtime.Proofs.InvariantSpace

set_option autoImplicit false

/-! # Runtime.Proofs.Adapters.Progress

Adapters from `ProtocolMachineInvariantSpace` to liveness/progress theorem APIs.
-/

namespace Runtime
namespace Proofs
namespace Adapters

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Extract the liveness bundle from invariant-space evidence (if present). -/
def toLivenessBundle? {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace (ν := ν) store₀ State) : Option (ProtocolMachineLivenessBundle store₀) :=
  space.liveness?

/-- Termination theorem instantiated from invariant-space evidence.
    Requires liveness bundle to be present. -/
theorem protocol_machine_termination_from_invariant_space
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace (ν := ν) store₀ State)
    (bundle : ProtocolMachineLivenessBundle store₀)
    (hLiveness : space.liveness? = some bundle) :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ bundle.fairness.k * protocolMachineMeasure store₀ := by
  simpa using protocol_machine_termination_from_bundle (bundle := bundle)

/-- If the invariant space includes liveness with optional progress evidence,
    derive enabledness at the initial state under non-terminality. -/
theorem protocol_machine_progress_from_invariant_space
    {store₀ : SessionStore ν} {State : Type v}
    (space : ProtocolMachineInvariantSpace (ν := ν) store₀ State)
    (bundle : ProtocolMachineLivenessBundle store₀)
    (hLiveness : space.liveness? = some bundle)
    (hNonTerminal : ¬ AllSessionsComplete store₀)
    (hHasProgress : bundle.progressHypothesis?.isSome = true) :
    ProgressEnabled store₀ := by
  simpa using
    protocol_machine_progress_from_optional_hypothesis (bundle := bundle)
      hNonTerminal hHasProgress

end

end Adapters
end Proofs
end Runtime
