
import Runtime.Proofs.TheoremPack.Build

/- ## Structured Block 1 -/
set_option autoImplicit false

/-! # Runtime.Proofs.Examples.DistributedProfiles

End-to-end protocol machine examples for distributed theorem spaces:
profile attachment in `ProtocolMachineInvariantSpaceWithProfiles` automatically materializes
the corresponding theorem artifact in `ProtocolMachineTheoremPack`.
-/

namespace Runtime
namespace Proofs
namespace Examples

universe u v

section

variable {ν : Type u} [VerificationModel ν]
variable {store₀ : SessionStore ν} {State : Type v}

/-- Minimal base invariant space used by theorem-pack examples. -/
def baseSpace (bundle : ProtocolMachineLivenessBundle store₀) :
    ProtocolMachineInvariantSpaceWithProfiles (ν := ν) store₀ State :=
  ProtocolMachineInvariantSpaceWithProfiles.mk
    (Adapters.ProtocolMachineInvariantSpaceWithDistributedProfiles.mk
      (ProtocolMachineInvariantSpace.mk (some bundle) none none none)
      {})
    {}

/-- Concrete BFT-style protocol spec used by the Byzantine/quorum bridge example. -/
def bftQuorumSpec : Distributed.ProtocolSpec :=
  { n := 4
  , f := 1
  , timing := .partialSync
  , evidenceAccumulation := .intersection
  , conflictExclusionLaw := .quorumIntersection
  , finalizationWitnessRule := .thresholdCertificate
  , witnessMonotonicity := true
  , certificate := .quorum
  , quorumSize := 3
  , authentication := .signatures
  , faultModel := .byzantine
  , partitionPolicy := .safetyFirst
  , deterministicFinality := true
  , timingAuthContractDeclared := true
  , quorumIntersectionWitnessed := true
  }

/-- The concrete BFT-style spec passes the regime-aware Byzantine admission gate. -/
theorem bft_quorum_spec_assumptions_passed :
    (Distributed.runAssumptionValidation
      bftQuorumSpec
      (Distributed.byzantineSafetyAssumptionsFor bftQuorumSpec)).allPassed = true := by
  rfl

/-! ## Concrete Timed Profiles -/

/-- Tiny partial-synchrony model whose timed-run predicates are explicit. -/
def timedPartialSynchronyModel :
    Distributed.PartialSynchrony.Model Nat Unit Unit Unit where
  initial := fun s => s = 0
  step := fun s _ => some s
  decide := fun _ => some ()
  messageDelayBoundedAfterGST := fun _ gst bound => gst = 0 ∧ bound = 0
  pacemakerFairAfterGST := fun _ gst => gst = 0
  leaderCorrectAfterGST := fun _ gst => gst = 0

/-- Proof-carrying timed assumptions for the tiny partial-synchrony model. -/
def timedPartialSynchronyAssumptions :
    Distributed.PartialSynchrony.Assumptions timedPartialSynchronyModel where
  FairRun := fun run => run 0 = 0
  gst := 0
  messageDelayBound := 0
  postGSTBound := 0
  postGSTMessageDelay := by
    intro _run _hFair _hInit
    exact ⟨rfl, rfl⟩
  fairPacemakerAfterGST := by
    intro _run _hFair _hInit
    rfl
  correctLeaderAfterGST := by
    intro _run _hFair _hInit
    rfl
  postGSTProgress := by
    intro _run _hFair _hInit
    exact ⟨0, Nat.le_refl 0, (), rfl⟩
  boundedWindowProgress := by
    intro _run _hFair _hInit
    exact ⟨0, Nat.le_refl 0, (), rfl⟩

/-- Concrete partial-synchrony profile used by theorem-pack examples. -/
def timedPartialSynchronyProfile : Distributed.PartialSynchrony.LivenessProtocol :=
  Distributed.PartialSynchrony.Profile.mk
    timedPartialSynchronyModel timedPartialSynchronyAssumptions

/-- Tiny responsiveness model whose optimistic timing predicates are explicit. -/
def timedResponsivenessModel :
    Distributed.Responsiveness.Model Nat Unit Unit Unit where
  initial := fun s => s = 0
  step := fun s _ => some s
  decide := fun _ => some ()
  optimisticNetworkWindow := fun _ gst bound => gst = 0 ∧ bound = 0
  authenticationStrongAfterGST := fun _ gst => gst = 0
  leaderResponsiveWindow := fun _ gst bound => gst = 0 ∧ bound = 0
  timeoutAdmissible := fun timeout _ => timeout = timeout

/-- Proof-carrying optimistic assumptions for the tiny responsiveness model. -/
def timedResponsivenessAssumptions :
    Distributed.Responsiveness.Assumptions timedResponsivenessModel where
  FairRun := fun run => run 0 = 0
  gst := 0
  optimisticBound := 0
  optimisticNetwork := by
    intro _run _hFair _hInit
    exact ⟨rfl, rfl⟩
  authenticationStrong := by
    intro _run _hFair _hInit
    rfl
  leaderQuality := by
    intro _run _hFair _hInit
    exact ⟨rfl, rfl⟩
  timeoutSchedule := by
    intro timeout _run _hFair _hInit
    rfl
  optimisticProgress := by
    intro _run _hFair _hInit
    exact ⟨0, Nat.le_refl 0, (), rfl⟩
  timeoutIndependentProgress := by
    intro _timeout _run _hFair _hInit _hTimeout _latencyTimeout
    exact ⟨0, Nat.le_refl 0, (), rfl⟩

/-- Concrete responsiveness profile used by theorem-pack examples. -/
def timedResponsivenessProfile : Distributed.Responsiveness.ResponsiveProtocol :=
  Distributed.Responsiveness.Profile.mk
    timedResponsivenessModel timedResponsivenessAssumptions

/-! ## Concrete Nakamoto Profile -/

/-- Tiny Nakamoto model with explicit chain, probability, churn, and quality semantics. -/
def tinyNakamotoModel : Distributed.Nakamoto.Model Nat Unit Unit where
  initial := fun s => s = 0
  chain := fun _ => [()]
  honestWeight := fun chain => chain.length
  failureProbabilityAtDepth := fun _ => 0
  adversarialPowerBounded := (0 : Nat) = 0
  churnWithin := fun _run churnBudget => 0 ≤ churnBudget

/-- Proof-carrying assumptions for the tiny Nakamoto model. -/
def tinyNakamotoAssumptions :
    Distributed.Nakamoto.Assumptions tinyNakamotoModel where
  AdmissibleRun := fun _run => (0 : Nat) = 0
  ε := 0
  settlementDepth := 0
  churnBudget := 0
  growthWindow := 0
  minGrowth := 0
  qualityWindow := 0
  minHonestWeight := 0
  probabilityBudget := by
    exact ⟨rfl, le_rfl⟩
  commonPrefix := by
    intro _run _hRun _i _j _pref _hij hPrefix _hDepth
    exact hPrefix
  chainGrowth := by
    intro _run _hRun _i
    exact Nat.le_refl _
  chainQuality := by
    intro _run _hRun _i
    exact Nat.zero_le _
  churnWithin := by
    intro _run _hRun
    exact Nat.zero_le _

/-- Concrete Nakamoto profile used by theorem-pack examples. -/
def tinyNakamotoProfile : Distributed.Nakamoto.SecurityProtocol :=
  Distributed.Nakamoto.Profile.mk tinyNakamotoModel tinyNakamotoAssumptions

/-! ## Concrete DA and Accountable-Safety Profiles -/

/-- Tiny DA model with one shard and a threshold reconstruction predicate. -/
def tinyDAModel : Distributed.DataAvailability.Model Unit Unit where
  n := 1
  k := 1
  shards := fun _ => [()]
  validShard := fun _ _ => (0 : Nat) = 0
  sampled := fun _ _ => (0 : Nat) = 0
  reconstructs := fun _ chunks => 1 ≤ chunks.length
  withheld := fun _ _ => (1 : Nat) = 0

/-- Proof-carrying assumptions for the tiny DA model. -/
def tinyDAAssumptions :
    Distributed.DataAvailability.Assumptions tinyDAModel where
  kOfNWellFormed := ⟨Nat.le_refl 1, Nat.succ_pos 0⟩
  samplingCoversValidShards := by
    intro _s _c _hMem _hValid
    rfl
  withholdingBound := by
    intro _s _c _hMem _hValid hWithheld
    exact Nat.succ_ne_zero 0 hWithheld
  reconstructionQuorumAvailable := by
    intro _s
    exact ⟨[()], Nat.le_refl 1, by intro _c _hMem; exact ⟨List.mem_singleton_self (), rfl, rfl⟩⟩
  reconstructionSound := by
    intro _s _chunks hQuorum
    exact hQuorum.1

/-- Concrete DA profile used by theorem-pack examples. -/
def tinyDAProfile : Distributed.DataAvailability.DAProtocol :=
  Distributed.DataAvailability.Profile.mk tinyDAModel tinyDAAssumptions

/-- Tiny accountable-safety model where every conflict constructs one fault evidence object. -/
def tinyAccountableModel :
    Distributed.AccountableSafety.Model Unit Bool Unit where
  conflicts := fun d₁ d₂ => d₁ ≠ d₂
  decided := fun _ _ => (0 : Nat) = 0
  faultEvidence := fun _ _ => (0 : Nat) = 0
  evidenceForConflict := fun _ _ _ _ => (0 : Nat) = 0
  verifies := fun _ _ => (0 : Nat) = 0
  slashable := fun _ => (0 : Nat) = 0

/-- Proof-carrying assumptions for the tiny accountable-safety model. -/
def tinyAccountableAssumptions :
    Distributed.AccountableSafety.Assumptions tinyAccountableModel where
  conflictEvidenceConstructible := by
    intro _s _d₁ _d₂ _hDec₁ _hDec₂ _hConflict
    exact ⟨(), rfl⟩
  evidenceIsFaultEvidence := by
    intro _s _d₁ _d₂ _f _hEvidence
    rfl
  evidenceVerifies := by
    intro _s _d₁ _d₂ _f _hEvidence
    rfl
  evidenceSlashable := by
    intro _s _d₁ _d₂ _f _hEvidence
    rfl

/-- Concrete accountable-safety profile used by theorem-pack examples. -/
def tinyAccountableProfile : Distributed.AccountableSafety.AccountableProtocol :=
  Distributed.AccountableSafety.Profile.mk tinyAccountableModel tinyAccountableAssumptions

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FLPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP p)
    ).flpLowerBound?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FLPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFLP p)
    ).flpImpossibility?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CAPProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCAP p)
    ).capImpossibility?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.QuorumGeometryProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDistributedProfiles
        { quorumGeometry? := some p })
    ).quorumGeometry?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.PartialSynchronyProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withPartialSynchrony p)
    ).partialSynchrony?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ResponsivenessProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withResponsiveness p)
    ).responsiveness?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withPartialSynchrony
          timedPartialSynchronyProfile)
    ).partialSynchrony?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withResponsiveness
          timedResponsivenessProfile)
    ).responsiveness?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.NakamotoProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withNakamoto p)
    ).nakamoto?.isSome = true := by
/- ## Structured Block 2 -/
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withNakamoto
          tinyNakamotoProfile)
    ).nakamoto?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ReconfigurationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withReconfiguration p)
    ).reconfiguration?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.AtomicBroadcastProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAtomicBroadcast p)
    ).atomicBroadcast?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.AccountableSafetyProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAccountableSafety p)
    ).accountableSafety?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withAccountableSafety
          tinyAccountableProfile)
    ).accountableSafety?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FailureDetectorsProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFailureDetectors p)
    ).failureDetectors?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.DataAvailabilityProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDataAvailability p)
    ).dataAvailability?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withDataAvailability
          tinyDAProfile)
    ).dataAvailability?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CoordinationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCoordination p)
    ).coordination?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CoordinationProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCoordination p)
    ).calm?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CRDTProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDT p)
    ).crdt?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CRDTProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDT p)
    ).crdtMonotonicity?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.CRDTErasureProfile) :
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withCRDTErasure p)
    ).crdtErasure?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.TriangleOfForgettingProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withTriangleOfForgetting p)
    ).triangleOfForgetting?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ByzantineSafetyProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withByzantineSafety p)
    ).byzantineSafety?.isSome = true := by
  rfl

/--
BFT path: a quorum-geometry profile induces a Byzantine-safety theorem-pack
artifact without the caller supplying a separate Byzantine safety theorem.
-/
example (bundle : ProtocolMachineLivenessBundle store₀) (q : Adapters.QuorumGeometryProfile) :
    let byz :=
      Distributed.ByzantineSafety.Profile.ofQuorumGeometry
        q bftQuorumSpec bft_quorum_spec_assumptions_passed
    (buildProtocolMachineTheoremPack
      (space :=
        (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withByzantineSafety byz)
    ).byzantineSafety?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ConsensusEnvelopeProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withConsensusEnvelope p)
    ).consensusEnvelope?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.FailureEnvelopeProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withFailureEnvelope p)
    ).failureEnvelope?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ProtocolMachineEnvelopeAdherenceProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withProtocolMachineEnvelopeAdherence p)
    ).protocolMachineEnvelopeAdherence?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ProtocolMachineEnvelopeAdmissionProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withProtocolMachineEnvelopeAdmission p)
    ).protocolMachineEnvelopeAdmission?.isSome = true := by
  rfl

example (bundle : ProtocolMachineLivenessBundle store₀) (p : Adapters.ProtocolEnvelopeBridgeProfile) :
    (buildProtocolMachineTheoremPack
      (space := (baseSpace (ν := ν) (store₀ := store₀) (State := State) bundle).withProtocolEnvelopeBridge p)
    ).protocolEnvelopeBridge?.isSome = true := by
  rfl

end

end Examples
end Proofs
end Runtime
