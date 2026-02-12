import Runtime.Adequacy.EnvelopeCore.FailureTaxonomy.Core

/-! # Failure Taxonomy Protocol Pack

Derived theorem extractions and the packaged protocol record built
on top of `FailureEnvelopePremises`. -/

set_option autoImplicit false

namespace Runtime
namespace Adequacy

universe u v

/-- Extract cross-target failure-envelope conformance theorem from failure premises. -/
theorem crossTargetFailureConformance_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CrossTargetFailureConformance
      p.failureVisible p.singleThreadRun p.multiThreadRun p.shardedRun :=
  p.crossTargetConformanceWitness

/-- Extract abstract recovery-action safety theorem from failure premises. -/
theorem recoveryActionSafety_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RecoveryActionSafety p.Safe p.recoveryStep :=
  p.recoveryActionSafetyWitness

/-- Extract abstract no-harmful-replay theorem from failure premises. -/
theorem noUnsafeReplay_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    NoUnsafeReplay p.Safe p.replayPre p.replay :=
  p.noUnsafeReplayWitness

/-- Extract checkpoint-restart refinement theorem from failure premises. -/
theorem checkpointRestartRefinement_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    CheckpointRestartRefinement p.Refines p.checkpoint p.restart :=
  p.checkpointRestartRefinementWitness

/-- Extract restart-refinement + structured-error adequacy from failure premises. -/
theorem restartStructuredErrorAdequacy_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    RestartRefinementStructuredErrorAdequacy
      p.Refines p.checkpoint p.restart p.structuredErrors :=
  p.restartStructuredErrorAdequacyWitness

/-- Extract failure-envelope soundness extension theorem from failure premises. -/
theorem failureEnvelopeSoundness_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeSoundnessExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeSoundnessWitness

/-- Extract failure-envelope maximality extension theorem from failure premises. -/
theorem failureEnvelopeMaximality_of_failurePremises
    {State : Type u} {Obs : Type v}
    (p : FailureEnvelopePremises State Obs) :
    FailureEnvelopeMaximalityExtension
      p.localEnvelope p.RefRun p.ImplRun p.injectFailure :=
  p.failureEnvelopeMaximalityWitness

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
      crossTargetFailureConformance_of_failurePremises premises
  recoveryActionSafety :
    RecoveryActionSafety premises.Safe premises.recoveryStep :=
      recoveryActionSafety_of_failurePremises premises
  noUnsafeReplay :
    NoUnsafeReplay premises.Safe premises.replayPre premises.replay :=
      noUnsafeReplay_of_failurePremises premises
  checkpointRestartRefinement :
    CheckpointRestartRefinement
      premises.Refines premises.checkpoint premises.restart :=
      checkpointRestartRefinement_of_failurePremises premises
  restartStructuredErrorAdequacy :
    RestartRefinementStructuredErrorAdequacy
      premises.Refines premises.checkpoint premises.restart premises.structuredErrors :=
      restartStructuredErrorAdequacy_of_failurePremises premises
  failureEnvelopeSoundness :
    FailureEnvelopeSoundnessExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failureEnvelopeSoundness_of_failurePremises premises
  failureEnvelopeMaximality :
    FailureEnvelopeMaximalityExtension
      premises.localEnvelope premises.RefRun premises.ImplRun premises.injectFailure :=
      failureEnvelopeMaximality_of_failurePremises premises



end Adequacy
end Runtime
