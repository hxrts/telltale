import Runtime.Adequacy.EnvelopeCore.FailureTaxonomy.Core

/-! # Failure Taxonomy Protocol Pack

Derived theorem extractions and the packaged protocol record built
on top of `FailureEnvelopePremises`. -/

set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

/-! ## Premise Projection Theorems I -/

/-- Extract cross-target failure-envelope conformance theorem from failure premises. -/
theorem cross_target_failure_conformance_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CrossTargetFailureConformance
      p.failureVisible p.singleThreadRun p.multiThreadRun p.shardedRun :=
  p.crossTargetConformanceWitness

/-- Extract abstract recovery-action safety theorem from failure premises. -/
theorem recovery_action_safety_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RecoveryActionSafety p.Safe p.recoveryStep :=
  p.recoveryActionSafetyWitness

/-- Extract abstract no-harmful-replay theorem from failure premises. -/
theorem no_unsafe_replay_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    NoUnsafeReplay p.Safe p.replayPre p.replay :=
  p.noUnsafeReplayWitness

/-- Extract checkpoint-restart refinement theorem from failure premises. -/
theorem checkpoint_restart_refinement_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CheckpointRestartRefinement p.Refines p.checkpoint p.restart :=
  p.checkpointRestartRefinementWitness

/-- Extract restart-refinement + structured-error adequacy from failure premises. -/
theorem restart_structured_error_adequacy_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RestartRefinementStructuredErrorAdequacy
      p.Refines p.checkpoint p.restart p.structuredErrors :=
  p.restartStructuredErrorAdequacyWitness

/-! ## Premise Projection Theorems II -/

/-- Extract failure-envelope soundness extension theorem from failure premises. -/
theorem failure_envelope_soundness_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeSoundnessExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeSoundnessWitness

/-- Extract failure-envelope maximality extension theorem from failure premises. -/
theorem failure_envelope_maximality_of_failure_premises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeMaximalityExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeMaximalityWitness

/-! ## Packaged Protocol Record -/

/-- Packaged abstract failure/recovery theorem family. -/
structure FailureEnvelopeProtocol where
  State : Type u
  Obs : Type v
  premises : FailureEnvelopePremises State Obs
  crossTargetConformance :
    CrossTargetFailureConformance
      premises.failureVisible
      premises.singleThreadRun
      premises.multiThreadRun
      premises.shardedRun :=
      cross_target_failure_conformance_of_failure_premises premises
  recoveryActionSafety :
    RecoveryActionSafety premises.Safe premises.recoveryStep :=
      recovery_action_safety_of_failure_premises premises
  noUnsafeReplay :
    NoUnsafeReplay premises.Safe premises.replayPre premises.replay :=
      no_unsafe_replay_of_failure_premises premises
  checkpointRestartRefinement :
    CheckpointRestartRefinement
      premises.Refines premises.checkpoint premises.restart :=
      checkpoint_restart_refinement_of_failure_premises premises
  restartStructuredErrorAdequacy :
    RestartRefinementStructuredErrorAdequacy
      premises.Refines premises.checkpoint premises.restart premises.structuredErrors :=
      restart_structured_error_adequacy_of_failure_premises premises
  failureEnvelopeSoundness :
    FailureEnvelopeSoundnessExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failure_envelope_soundness_of_failure_premises premises
  failureEnvelopeMaximality :
    FailureEnvelopeMaximalityExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failure_envelope_maximality_of_failure_premises premises



end Adequacy
end Runtime
