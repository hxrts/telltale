
import Runtime.Proofs.TheoremPack.Build
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

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

/-- Parameters for the partial-synchrony example: 4 parties (`f = 1`), views
of length 2, post-GST delay bound 1, GST at time 4. -/
def psParams : Distributed.PartialSynchrony.Rounds.Params :=
  { n := 4, f := 1, viewLen := 2, delta := 1, gst := 4 }

/-- Example run: party 1 is Byzantine and never votes; every leader proposes 7;
before GST every delay is 5 (views time out), after GST every delay is 1. -/
def psRun : Distributed.PartialSynchrony.Rounds.RoundRun where
  honest := fun p => p != 1
  proposalTo := fun _ _ => 7
  proposeDelay := fun v _ => if v * 2 < 4 then 5 else 1
  voteDelay := fun v _ => if v * 2 < 4 then 5 else 1
  byzVote := fun _ _ => none

/-- Abstract model over time `t : Nat`: value 7 is reported once some view of
`psRun` ending by time `t` has a vote quorum for 7. -/
def timedPartialSynchronyModel :
    Distributed.PartialSynchrony.Model Nat Unit Unit Unit where
  initial := fun s => s = 0
  step := fun s _ => some (s + 1)
  decide := fun t =>
    if ∃ v, v < t ∧ Distributed.PartialSynchrony.Rounds.ViewDecides psParams psRun v 7 ∧
        (v + 1) * 2 ≤ t then some () else none

/-- `psRun` respects the post-GST delay bound. -/
theorem psRun_admissible : Distributed.PartialSynchrony.Rounds.Admissible psParams psRun := by
  intro v _ hv
  simp only [psParams] at hv
  simp [psRun, psParams, show ¬ v * 2 < 4 by omega]

/-- `psRun` has one Byzantine party and constant (hence consistent) proposals. -/
theorem psRun_wellFormed : Distributed.PartialSynchrony.Rounds.WellFormed psParams psRun :=
  ⟨by unfold Distributed.PartialSynchrony.Rounds.FaultBound; decide, fun _ _ _ => rfl⟩

/-- Fair runs are the identity clock; they refine `psRun`. Any decided value is
an honest party's received proposal, hence 7. -/
def timedPartialSynchronyAssumptions :
    Distributed.PartialSynchrony.Assumptions timedPartialSynchronyModel where
  FairRun := fun run => run = id
  params := psParams
  timing := by decide
  realizedByRounds := by
    rintro run rfl _
    refine ⟨psRun, psRun_admissible, psRun_wellFormed, ?_⟩
    rintro t ⟨v, x, hv, hle⟩
    obtain ⟨p, _, rfl⟩ := Distributed.PartialSynchrony.Rounds.decided_value_proposed
      psParams psRun (by decide) psRun_wellFormed.1 hv
    refine ⟨(), ?_⟩
    simp only [psParams] at hle
    simp only [timedPartialSynchronyModel, id]
    exact ite_eq_left_iff.2 fun h => absurd ⟨v, by omega, hv, hle⟩ h

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

/-- Production schedule: every third round (`t % 3 = 2`) is adversarial. -/
def nkSched (t : Nat) : Bool := t % 3 != 2

/-- Any three consecutive rounds contain exactly one adversarial round. -/
theorem nk_adv_three (s n : Nat) :
    Distributed.Nakamoto.LongestChain.advIn nkSched s (n + 3) =
      Distributed.Nakamoto.LongestChain.advIn nkSched s n + 1 := by
  simp only [Distributed.Nakamoto.LongestChain.advIn, nkSched]
  rw [show s + (n + 1) = s + n + 1 by omega, show s + (n + 2) = s + n + 2 by omega]
  simp only [bne_iff_ne, ne_eq]
  split_ifs <;> omega

/-- Adversarial rounds in a window of `n` rounds are at most `⌈n/3⌉`. -/
theorem nk_adv_le (s n : Nat) :
    Distributed.Nakamoto.LongestChain.advIn nkSched s n ≤ (n + 2) / 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [Distributed.Nakamoto.LongestChain.advIn]
    | 1 => simp only [Distributed.Nakamoto.LongestChain.advIn]; split <;> omega
    | 2 =>
      simp only [Distributed.Nakamoto.LongestChain.advIn, nkSched, bne_iff_ne, ne_eq]
      split_ifs <;> omega
    | m + 3 => rw [nk_adv_three]; have := ih m (by omega); omega

/-- The schedule has an honest (weak) majority in every window of `≥ 2` rounds. -/
theorem nk_window (T : Nat) :
    Distributed.Nakamoto.LongestChain.WindowHonestMajorityUpTo nkSched 2 T := by
  intro s _ n _ _ hn
  have h1 := nk_adv_le s n
  have h2 := Distributed.Nakamoto.LongestChain.honestIn_add_advIn nkSched s n
  omega

/-- Longest-chain execution of `nkSched` (block `t` is minted as `t`) in which
the adversary always withholds its private branch. -/
def nkExec : Nat → Distributed.Nakamoto.LongestChain.LCState Nat
  | 0 => Distributed.Nakamoto.LongestChain.init
  | t + 1 => Distributed.Nakamoto.LongestChain.produce nkSched id t (nkExec t)

/-- `nkExec` is a run of the longest-chain protocol. -/
theorem nkExec_isRun : Distributed.Nakamoto.LongestChain.IsRun nkSched id nkExec :=
  ⟨rfl, fun _ => Distributed.Nakamoto.LongestChain.AdvAct.wait _⟩

/-- Nakamoto model over time: the observed chain is the public chain of `nkExec`. -/
def tinyNakamotoModel : Distributed.Nakamoto.Model Nat Nat Unit where
  initial := fun s => s = 0
  chain := fun t => (nkExec t).pub
  failureProbabilityAtDepth := fun _ => 0
  adversarialPowerBounded :=
    Distributed.Nakamoto.LongestChain.WindowHonestMajorityUpTo nkSched 2 12

/-- Assumptions: admissible runs are the identity clock, realised by `nkExec`. -/
def tinyNakamotoAssumptions :
    Distributed.Nakamoto.Assumptions tinyNakamotoModel where
  AdmissibleRun := fun run => run = id
  ε := 0
  settlementDepth := 2
  probabilityBudget := ⟨nk_window 12, le_rfl⟩
  realizedByLongestChain := by
    rintro run rfl
    exact ⟨nkSched, id, nkExec, nkExec_isRun, nk_window, fun _ => rfl⟩

/-- Concrete Nakamoto profile used by theorem-pack examples. -/
def tinyNakamotoProfile : Distributed.Nakamoto.SecurityProtocol :=
  Distributed.Nakamoto.Profile.mk tinyNakamotoModel tinyNakamotoAssumptions

/-! ## Concrete DA and Accountable-Safety Profiles -/

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

open Polynomial in
/-- Reed–Solomon DA example over `ZMod 5`: data `X + 1` (degree 1, `k = 2`),
three shards at points `0, 1, 2`, custodian `i` holds shard `i`; custodian 2
is Byzantine and withholds its shard. The commitment is an ideal one whose
check is the true evaluation, so `CommitmentBinding` holds by construction. -/
noncomputable def tinyDAModel : Distributed.DataAvailability.Model (ZMod 5) (Fin 3) where
  n := 3
  k := 2
  points := fun i => (i.val : ZMod 5)
  data := X + C 1
  custody := id
  response := fun p =>
    if p = 2 then none else some ((X + C 1 : (ZMod 5)[X]).eval (p.val : ZMod 5))
  verify := fun i y => y = (X + C 1 : (ZMod 5)[X]).eval (i.val : ZMod 5)

open Polynomial in
/-- Assumptions for the DA example: honest custodians `{0, 1}`. -/
noncomputable def tinyDAAssumptions :
    Distributed.DataAvailability.Assumptions tinyDAModel where
  honest := {0, 1}
  pointsInjective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; revert h; decide)
  dataDegree := by
    show (X + C (1 : ZMod 5)).degree < ((2 : Nat) : WithBot Nat)
    rw [degree_X_add_C]; exact_mod_cast (by norm_num : (1 : Nat) < 2)
  binding := fun _ _ h => h
  verifyComplete := fun _ => rfl
  honestServes := by
    intro p hp
    fin_cases p <;> simp_all [tinyDAModel]
  custodyDistinct := fun _ _ _ _ h => h
  honestCustodians := by decide

/-- Concrete DA profile used by theorem-pack examples. -/
noncomputable def tinyDAProfile : Distributed.DataAvailability.DAProtocol :=
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
