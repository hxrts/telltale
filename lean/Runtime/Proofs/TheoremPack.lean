import Runtime.Proofs.Adapters.Progress
import Runtime.Proofs.Adapters.Distributed
import Runtime.Proofs.Adapters.Classical
import Runtime.Proofs.DeterminismApi

set_option autoImplicit false

/-! # Runtime.Proofs.TheoremPack

One-shot theorem packaging from a VM invariant space carrying distributed and
classical optional profiles.
-/

namespace Runtime
namespace Proofs

universe u v

section

variable {ν : Type u} [VerificationModel ν]

/-- Combined invariant space carrying distributed and classical profiles. -/
structure VMInvariantSpaceWithProfiles
    (store₀ : SessionStore ν) (State : Type v)
    extends Adapters.VMInvariantSpaceWithDistributed (ν := ν) store₀ State where
  classical : Adapters.ClassicalProfiles State := {}

/-- Forget classical profiles and view the space as distributed-only. -/
def VMInvariantSpaceWithProfiles.toDistributedSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.VMInvariantSpaceWithDistributed store₀ State :=
  { toVMInvariantSpace := space.toVMInvariantSpace
  , distributed := space.distributed
  }

/-- Forget distributed profiles and view the space as classical-only. -/
def VMInvariantSpaceWithProfiles.toClassicalSpace
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    Adapters.VMInvariantSpaceWithClassical store₀ State :=
  { toVMInvariantSpace := space.toVMInvariantSpace
  , classical := space.classical
  }

/-- Attach distributed profiles to a combined space. -/
def VMInvariantSpaceWithProfiles.withDistributedProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (distributed : Adapters.DistributedProfiles) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := distributed }

/-- Attach classical profiles to a combined space. -/
def VMInvariantSpaceWithProfiles.withClassicalProfiles
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (classical : Adapters.ClassicalProfiles State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with classical := classical }

/-- Attach an FLP distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFLP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FLPProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with flp? := some p } }

/-- Attach a CAP distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCAP
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CAPProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with cap? := some p } }

/-- Attach a quorum-geometry distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withQuorumGeometry
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.QuorumGeometryProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with quorumGeometry? := some p } }

/-- Attach a partial-synchrony distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withPartialSynchrony
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.PartialSynchronyProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with partialSynchrony? := some p } }

/-- Attach a responsiveness distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withResponsiveness
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ResponsivenessProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with responsiveness? := some p } }

/-- Attach a Nakamoto distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withNakamoto
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.NakamotoProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with nakamoto? := some p } }

/-- Attach a reconfiguration distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withReconfiguration
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.ReconfigurationProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with reconfiguration? := some p } }

/-- Attach an atomic-broadcast distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withAtomicBroadcast
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AtomicBroadcastProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with atomicBroadcast? := some p } }

/-- Attach an accountable-safety distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withAccountableSafety
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.AccountableSafetyProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with accountableSafety? := some p } }

/-- Attach a failure-detector distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFailureDetectors
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FailureDetectorsProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with failureDetectors? := some p } }

/-- Attach a data-availability distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withDataAvailability
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.DataAvailabilityProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with dataAvailability? := some p } }

/-- Attach a coordination distributed profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withCoordination
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.CoordinationProfile) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with distributed := { space.distributed with coordination? := some p } }

/-- Attach a Foster profile to a combined space. -/
def VMInvariantSpaceWithProfiles.withFoster
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State)
    (p : Adapters.FosterProfile State) :
    VMInvariantSpaceWithProfiles store₀ State :=
  { space with classical := { space.classical with foster? := some p } }

/-- Packaged FLP lower-bound artifact. -/
structure FLPLowerBoundArtifact where
  protocol : Distributed.FLP.ImpossibilityProtocol
  proof : ∃ run, protocol.premises.FairRun run ∧ ∀ n, protocol.premises.Uncommitted (run n)

/-- Packaged FLP impossibility artifact. -/
structure FLPImpossibilityArtifact where
  protocol : Distributed.FLP.ImpossibilityProtocol
  proof : ¬ Distributed.FLP.TerminatesOnAllFairRuns protocol.model protocol.premises.FairRun

/-- Packaged CAP impossibility artifact. -/
structure CAPImpossibilityArtifact where
  protocol : Distributed.CAP.ImpossibilityProtocol
  proof : ¬ Distributed.CAP.CAPGuarantee protocol.model protocol.premises.PartitionRun

/-- Packaged quorum-geometry safety artifact. -/
structure QuorumGeometryArtifact where
  protocol : Distributed.QuorumGeometry.SafetyProtocol
  noConflictingCommits :
    ∀ {s d₁ d₂},
      Distributed.QuorumGeometry.Committed protocol.model s d₁ →
      Distributed.QuorumGeometry.Committed protocol.model s d₂ →
      ¬ protocol.model.conflicts d₁ d₂
  forkExclusion :
    ∀ s, ¬ Distributed.QuorumGeometry.Forked protocol.model s
  safeFinality :
    ∀ {s d},
      Distributed.QuorumGeometry.Finalized protocol.model s d →
      ∀ d', Distributed.QuorumGeometry.Committed protocol.model s d' →
        ¬ protocol.model.conflicts d d'

/-- Packaged partial-synchrony liveness artifact. -/
structure PartialSynchronyArtifact where
  protocol : Distributed.PartialSynchrony.LivenessProtocol
  eventualDecision :
    Distributed.PartialSynchrony.TerminatesOnAllFairRuns
      protocol.model protocol.premises.FairRun
  boundedPostGST :
    Distributed.PartialSynchrony.BoundedTerminationAfterGST
      protocol.model protocol.premises.FairRun
      protocol.premises.gst protocol.premises.postGSTBound

/-- Packaged responsiveness artifact. -/
structure ResponsivenessArtifact where
  protocol : Distributed.Responsiveness.ResponsiveProtocol
  eventualDecision :
    Distributed.Responsiveness.TerminatesOnAllFairRuns
      protocol.model protocol.premises.FairRun
  timeoutIndependentLatency :
    Distributed.Responsiveness.TimeoutIndependentLatencyBound
      protocol.model protocol.premises.FairRun
      protocol.premises.gst protocol.premises.optimisticBound

/-- Packaged Nakamoto-security artifact. -/
structure NakamotoArtifact where
  protocol : Distributed.Nakamoto.SecurityProtocol
  probabilisticSafety :
    Distributed.Nakamoto.ProbabilisticSafety
      protocol.model protocol.premises.AdmissibleRun protocol.premises.ε
  settlementFinality :
    Distributed.Nakamoto.SettlementDepthFinality
      protocol.model protocol.premises.AdmissibleRun protocol.premises.settlementDepth
  livenessUnderChurn :
    Distributed.Nakamoto.LivenessUnderChurn
      protocol.model protocol.premises.AdmissibleRun protocol.premises.churnBudget

/-- Packaged reconfiguration artifact. -/
structure ReconfigurationArtifact where
  protocol : Distributed.Reconfiguration.ReconfigurationProtocol
  noSplitBrain :
    Distributed.Reconfiguration.NoSplitBrainAcrossReconfiguration protocol.model
  safeHandoff :
    Distributed.Reconfiguration.SafeHandoff protocol.model
  livenessPreserved :
    Distributed.Reconfiguration.LivenessPreserved protocol.model

/-- Packaged atomic-broadcast artifact. -/
structure AtomicBroadcastArtifact where
  protocol : Distributed.AtomicBroadcast.AtomicBroadcastProtocol
  totalOrderConsistency :
    Distributed.AtomicBroadcast.TotalOrderConsistency protocol.model
  logPrefixCompatibility :
    Distributed.AtomicBroadcast.LogPrefixCompatibility protocol.model
  consensusAtomicBroadcastBridge :
    Distributed.AtomicBroadcast.ConsensusAtomicBroadcastBridge protocol.model

/-- Packaged accountable-safety artifact. -/
structure AccountableSafetyArtifact where
  protocol : Distributed.AccountableSafety.AccountableProtocol
  accountableSafety :
    Distributed.AccountableSafety.AccountableSafety protocol.model

/-- Packaged failure-detector boundary artifact. -/
structure FailureDetectorsArtifact where
  protocol : Distributed.FailureDetectors.BoundaryProtocol
  solvabilityBoundary :
    Distributed.FailureDetectors.SolvableBoundary
      protocol.model protocol.premises.detector
  impossibilityBoundary :
    Distributed.FailureDetectors.ImpossibilityBoundary
      protocol.model protocol.premises.detector

/-- Packaged data-availability artifact. -/
structure DataAvailabilityArtifact where
  protocol : Distributed.DataAvailability.DAProtocol
  availability :
    Distributed.DataAvailability.DataAvailability protocol.model
  retrievability :
    Distributed.DataAvailability.DataRetrievability protocol.model

/-- Packaged coordination-characterization artifact. -/
structure CoordinationArtifact where
  protocol : Distributed.Coordination.CoordinationProtocol
  characterization :
    Distributed.Coordination.CoordinationCharacterization protocol.model

/-- Packaged VM termination artifact (when liveness bundle is provided). -/
structure TerminationArtifact {store₀ : SessionStore ν} where
  bundle : VMLivenessBundle store₀
  proof :
    ∃ (n : Nat) (store_final : SessionStore ν),
      store_final = executeSchedule bundle.model.step store₀ bundle.fairness.sched n ∧
      AllSessionsComplete store_final ∧
      n ≤ bundle.fairness.k * vmMeasure store₀

/-- Packaged output-condition soundness artifact. -/
structure OutputConditionArtifact where
  witness : OutputConditionWitness
  soundness : ∀ claim, witness.verify claim = true → witness.accepted claim

/-- Theorem pack auto-derived from a profile-carrying VM invariant space. -/
structure VMTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) where
  termination? : Option (TerminationArtifact (ν := ν) (store₀ := store₀))
  outputCondition? : Option OutputConditionArtifact
  flpLowerBound? : Option FLPLowerBoundArtifact
  flpImpossibility? : Option FLPImpossibilityArtifact
  capImpossibility? : Option CAPImpossibilityArtifact
  quorumGeometry? : Option QuorumGeometryArtifact
  partialSynchrony? : Option PartialSynchronyArtifact
  responsiveness? : Option ResponsivenessArtifact
  nakamoto? : Option NakamotoArtifact
  reconfiguration? : Option ReconfigurationArtifact
  atomicBroadcast? : Option AtomicBroadcastArtifact
  accountableSafety? : Option AccountableSafetyArtifact
  failureDetectors? : Option FailureDetectorsArtifact
  dataAvailability? : Option DataAvailabilityArtifact
  coordination? : Option CoordinationArtifact
  foster? : Option (Adapters.FosterArtifact State)
  maxWeight? : Option Adapters.MaxWeightArtifact
  ldp? : Option Adapters.LDPArtifact
  meanField? : Option Adapters.MeanFieldArtifact
  heavyTraffic? : Option Adapters.HeavyTrafficArtifact
  mixing? : Option Adapters.MixingArtifact
  fluid? : Option Adapters.FluidArtifact
  concentration? : Option Adapters.ConcentrationArtifact
  littlesLaw? : Option Adapters.LittlesLawArtifact
  functionalCLT? : Option Adapters.FunctionalCLTArtifact

/-- Build theorem artifacts from one invariant space. -/
def buildVMTheoremPack
    {store₀ : SessionStore ν} {State : Type v}
    (space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State) :
    VMTheoremPack space :=
  let termination? :=
    match space.toVMInvariantSpace.liveness? with
    | none => none
    | some bundle =>
        some
          { bundle := bundle
          , proof := by
              simpa using vm_termination_from_bundle (bundle := bundle)
          }
  let outputCondition? :=
    match space.toVMInvariantSpace.outputConditionWitness? with
    | none => none
    | some w =>
        some
          { witness := w
          , soundness := w.sound
          }
  let flpLowerBound? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p.protocol, proof := p.protocol.lowerBound }
  let flpImpossibility? :=
    match space.distributed.flp? with
    | none => none
    | some p => some { protocol := p.protocol, proof := p.protocol.impossibility }
  let capImpossibility? :=
    match space.distributed.cap? with
    | none => none
    | some p => some { protocol := p.protocol, proof := p.protocol.impossibility }
  let quorumGeometry? :=
    match space.distributed.quorumGeometry? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , noConflictingCommits := p.protocol.noConflictingCommits
          , forkExclusion := p.protocol.forkExclusion
          , safeFinality := p.protocol.safeFinality
          }
  let partialSynchrony? :=
    match space.distributed.partialSynchrony? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , eventualDecision := p.protocol.eventualDecision
          , boundedPostGST := p.protocol.boundedPostGST
          }
  let responsiveness? :=
    match space.distributed.responsiveness? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , eventualDecision := p.protocol.eventualDecision
          , timeoutIndependentLatency := p.protocol.timeoutIndependentLatency
          }
  let nakamoto? :=
    match space.distributed.nakamoto? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , probabilisticSafety := p.protocol.probabilisticSafety
          , settlementFinality := p.protocol.settlementFinality
          , livenessUnderChurn := p.protocol.livenessUnderChurn
          }
  let reconfiguration? :=
    match space.distributed.reconfiguration? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , noSplitBrain := p.protocol.noSplitBrain
          , safeHandoff := p.protocol.safeHandoff
          , livenessPreserved := p.protocol.livenessPreserved
          }
  let atomicBroadcast? :=
    match space.distributed.atomicBroadcast? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , totalOrderConsistency := p.protocol.totalOrderConsistency
          , logPrefixCompatibility := p.protocol.logPrefixCompatibility
          , consensusAtomicBroadcastBridge := p.protocol.consensusAtomicBroadcastBridge
          }
  let accountableSafety? :=
    match space.distributed.accountableSafety? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , accountableSafety := p.protocol.accountableSafety
          }
  let failureDetectors? :=
    match space.distributed.failureDetectors? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , solvabilityBoundary := p.protocol.solvabilityBoundary
          , impossibilityBoundary := p.protocol.impossibilityBoundary
          }
  let dataAvailability? :=
    match space.distributed.dataAvailability? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , availability := p.protocol.availability
          , retrievability := p.protocol.retrievability
          }
  let coordination? :=
    match space.distributed.coordination? with
    | none => none
    | some p =>
        some
          { protocol := p.protocol
          , characterization := p.protocol.characterization
          }
  let classicalPack := Adapters.buildVMClassicalTheoremPack (space := space.toClassicalSpace)
  { termination? := termination?
  , outputCondition? := outputCondition?
  , flpLowerBound? := flpLowerBound?
  , flpImpossibility? := flpImpossibility?
  , capImpossibility? := capImpossibility?
  , quorumGeometry? := quorumGeometry?
  , partialSynchrony? := partialSynchrony?
  , responsiveness? := responsiveness?
  , nakamoto? := nakamoto?
  , reconfiguration? := reconfiguration?
  , atomicBroadcast? := atomicBroadcast?
  , accountableSafety? := accountableSafety?
  , failureDetectors? := failureDetectors?
  , dataAvailability? := dataAvailability?
  , coordination? := coordination?
  , foster? := classicalPack.foster?
  , maxWeight? := classicalPack.maxWeight?
  , ldp? := classicalPack.ldp?
  , meanField? := classicalPack.meanField?
  , heavyTraffic? := classicalPack.heavyTraffic?
  , mixing? := classicalPack.mixing?
  , fluid? := classicalPack.fluid?
  , concentration? := classicalPack.concentration?
  , littlesLaw? := classicalPack.littlesLaw?
  , functionalCLT? := classicalPack.functionalCLT?
  }

/-- Compact theorem inventory for quick diagnostics. -/
def theoremInventory
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : List (String × Bool) :=
  [ ("termination", pack.termination?.isSome)
  , ("output_condition_soundness", pack.outputCondition?.isSome)
  , ("flp_lower_bound", pack.flpLowerBound?.isSome)
  , ("flp_impossibility", pack.flpImpossibility?.isSome)
  , ("cap_impossibility", pack.capImpossibility?.isSome)
  , ("quorum_geometry_safety", pack.quorumGeometry?.isSome)
  , ("partial_synchrony_liveness", pack.partialSynchrony?.isSome)
  , ("responsiveness", pack.responsiveness?.isSome)
  , ("nakamoto_security", pack.nakamoto?.isSome)
  , ("reconfiguration_safety", pack.reconfiguration?.isSome)
  , ("atomic_broadcast_ordering", pack.atomicBroadcast?.isSome)
  , ("accountable_safety", pack.accountableSafety?.isSome)
  , ("failure_detector_boundaries", pack.failureDetectors?.isSome)
  , ("data_availability_retrievability", pack.dataAvailability?.isSome)
  , ("coordination_characterization", pack.coordination?.isSome)
  , ("classical_foster", pack.foster?.isSome)
  , ("classical_maxweight", pack.maxWeight?.isSome)
  , ("classical_ldp", pack.ldp?.isSome)
  , ("classical_mean_field", pack.meanField?.isSome)
  , ("classical_heavy_traffic", pack.heavyTraffic?.isSome)
  , ("classical_mixing", pack.mixing?.isSome)
  , ("classical_fluid", pack.fluid?.isSome)
  , ("classical_concentration", pack.concentration?.isSome)
  , ("classical_littles_law", pack.littlesLaw?.isSome)
  , ("classical_functional_clt", pack.functionalCLT?.isSome)
  ]

/-- Theorem inventory extended with determinism artifacts. -/
def theoremInventoryWithDeterminism
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (determinism : VMDeterminismArtifacts) : List (String × Bool) :=
  theoremInventory (space := space) pack ++
    determinismInventory determinism

end

end Proofs
end Runtime
