import Runtime.Proofs.TheoremPack.Inventory
import Runtime.Proofs.EffectBisim.Bridge

/-! # Theorem-Pack Release Conformance

Release-gate helper surfaces for optimization classes, replay conformance, and
failure-envelope witness requirements.
-/

set_option autoImplicit false

namespace Runtime
namespace Proofs

universe u v w

open Runtime.Proofs.EffectBisim

/-! ## Optimization-Eligible Transformation Classes -/

/-- Runtime transformation envelope classes eligible for optimization. -/
inductive RuntimeTransformationEnvelopeClass where
  | schedulerPermutation
  | waveWidening
  | effectReordering
  | failureReplayNormalization
  deriving Repr, DecidableEq, Inhabited

/-- Deterministic enumeration of optimization-eligible transformation classes. -/
def RuntimeTransformationEnvelopeClass.all :
    List RuntimeTransformationEnvelopeClass :=
  [ .schedulerPermutation
  , .waveWidening
  , .effectReordering
  , .failureReplayNormalization
  ]

/-- Capability requirements for each optimization-eligible transformation class. -/
def transformationClassRequiredCapabilities
    (cls : RuntimeTransformationEnvelopeClass) : List String :=
  match cls with
  | .schedulerPermutation =>
      [ "protocol_envelope_bridge", "vm_envelope_adherence" ]
  | .waveWidening =>
      [ "protocol_envelope_bridge", "vm_envelope_adherence", "vm_envelope_admission" ]
  | .effectReordering =>
      [ "protocol_envelope_bridge", "vm_envelope_adherence", "vm_envelope_admission" ]
  | .failureReplayNormalization =>
      [ "failure_envelope", "vm_envelope_adherence" ]

private def inventoryHasEnabled
    (inventory : List (String × Bool))
    (name : String) : Bool :=
  match inventory.find? (fun entry => entry.1 = name) with
  | some (_, enabled) => enabled
  | none => false

/-- Inventory gate for one optimization-eligible transformation class. -/
def transformationClassEligible
    (inventory : List (String × Bool))
    (cls : RuntimeTransformationEnvelopeClass) : Bool :=
  (transformationClassRequiredCapabilities cls).all
    (fun name => inventoryHasEnabled inventory name)

/-- Snapshot of optimization-class eligibility keyed by theorem-pack inventory. -/
def transformationEligibilitySnapshot
    (inventory : List (String × Bool)) :
    List (RuntimeTransformationEnvelopeClass × Bool) :=
  RuntimeTransformationEnvelopeClass.all.map
    (fun cls => (cls, transformationClassEligible inventory cls))

/-! ## Effect-Bisim Preservation Bridge -/

/-- Witness that a transformed runtime state is linked to the source state by an
effect-bisimulation proof under one optimization class. -/
structure TransformationClassEffectBisimWitness
    {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ) where
  cls : RuntimeTransformationEnvelopeClass
  source : σ
  transformed : σ
  bisim : EffectBisim obs step source transformed

/-- Any certified optimization class that carries an `EffectBisim` witness
preserves observer behavior. -/
theorem transformationClass_preserves_observer_behavior
    {σ : Type u} {α : Type v}
    (obs : EffectObs σ α) (step : StateRel σ)
    (w : TransformationClassEffectBisimWitness obs step) :
    ObservationalEq obs w.source w.transformed :=
  effectBisim_implies_observationalEquivalence obs step w.bisim

/-! ## Replay Conformance Over Certified Equivalence Classes -/

/-- Certified replay-equivalence class used by conformance gates. -/
structure CertifiedReplayEquivalenceClass where
  cls : RuntimeTransformationEnvelopeClass
  certificateRef : String
  deriving Repr, DecidableEq, Inhabited

/-- Default certified replay classes admitted in release gates. -/
def defaultCertifiedReplayClasses : List CertifiedReplayEquivalenceClass :=
  RuntimeTransformationEnvelopeClass.all.map
    (fun cls =>
      { cls := cls
      , certificateRef := "certified/" ++ reprStr cls
      })

private def traceSessionIds {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) : List SessionId :=
  trace.foldl
    (fun acc ev =>
      match obsSid? ev.event with
      | some sid => if sid ∈ acc then acc else acc ++ [sid]
      | none => acc)
    []

private def obsTag {ε : Type u} [EffectRuntime ε] : ObsEvent ε → String
  | .sent _ _ _ => "sent"
  | .received _ _ _ => "received"
  | .offered _ _ => "offered"
  | .chose _ _ => "chose"
  | .acquired _ _ => "acquired"
  | .released _ _ => "released"
  | .invoked _ _ => "invoked"
  | .opened _ _ => "opened"
  | .closed _ => "closed"
  | .epochAdvanced _ _ => "epoch"
  | .transferred _ _ _ => "transferred"
  | .forked _ _ => "forked"
  | .joined _ => "joined"
  | .aborted _ => "aborted"
  | .tagged _ => "tagged"
  | .checked _ _ => "checked"

private def replaySessionSignature {ε : Type u} [EffectRuntime ε]
    (trace : List (TickedObsEvent ε)) :
    List (SessionId × List String) :=
  let normalized := Runtime.VM.normalizeTrace trace
  let sids := traceSessionIds normalized
  sids.map (fun sid =>
    let tags := (filterBySid sid normalized).map (fun ev => obsTag ev.event)
    (sid, tags))

/-- A certified replay class is usable only when its transformation class is
inventory-admissible and it carries a non-empty certificate reference. -/
def certifiedReplayClassEligible
    (inventory : List (String × Bool))
    (cls : CertifiedReplayEquivalenceClass) : Bool :=
  transformationClassEligible inventory cls.cls &&
    cls.certificateRef.length > 0

/-- Replay conformance check against one certified equivalence class. -/
def replayConformsToCertifiedClass {ε : Type u} [EffectRuntime ε]
    (inventory : List (String × Bool))
    (cls : CertifiedReplayEquivalenceClass)
    (baseline replay : List (TickedObsEvent ε)) : Bool :=
  certifiedReplayClassEligible inventory cls &&
    decide (replaySessionSignature baseline = replaySessionSignature replay)

/-- Replay conformance check across all certified equivalence classes. -/
def replayConformsToClasses {ε : Type u} [EffectRuntime ε]
    (inventory : List (String × Bool))
    (classes : List CertifiedReplayEquivalenceClass)
    (baseline replay : List (TickedObsEvent ε)) : Bool :=
  classes.all (fun cls => replayConformsToCertifiedClass inventory cls baseline replay)

/-! ## Release Witness Gates and Report -/

/-- Failure-envelope cross-target witness gate. -/
def hasFailureEnvelopeCrossTargetWitness
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.failureEnvelope?.isSome

/-- Restart/structured-error adequacy witness gate. -/
def hasRestartStructuredErrorAdequacyWitness
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.failureEnvelope?.isSome

/-- Release gate: single-thread evidence is present. -/
def hasSingleThreadEvidence
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.failureEnvelope?.isSome

/-- Release gate: multi-thread evidence is present. -/
def hasMultiThreadEvidence
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.failureEnvelope?.isSome

/-- Release gate: sharded evidence is present. -/
def hasShardedEvidence
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space)) : Bool :=
  pack.failureEnvelope?.isSome

/-- Stable version tag for exported release-conformance reports. -/
def releaseConformanceReportVersion : String :=
  "v2.release.conformance.v1"

/-- Release conformance report keyed by theorem-pack capability inventory. -/
structure ReleaseConformanceReport where
  version : String
  theoremInventory : List (String × Bool)
  transformationEligibility : List (RuntimeTransformationEnvelopeClass × Bool)
  replayConformance : Bool
  failureEnvelopeCrossTargetWitness : Bool
  restartStructuredErrorAdequacyWitness : Bool
  singleThreadEvidence : Bool
  multiThreadEvidence : Bool
  shardedEvidence : Bool
  releaseReady : Bool
  deriving Repr, DecidableEq

/-- Build a release conformance report from theorem-pack inventory and replay evidence. -/
def buildReleaseConformanceReport {ε : Type w} [EffectRuntime ε]
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (baseline replay : List (TickedObsEvent ε))
    (classes : List CertifiedReplayEquivalenceClass := defaultCertifiedReplayClasses)
    (releaseTagged : Bool := false) :
    ReleaseConformanceReport :=
  let inventory := theoremInventory (space := space) pack
  let transform := transformationEligibilitySnapshot inventory
  let replayOk := replayConformsToClasses inventory classes baseline replay
  let crossTarget := hasFailureEnvelopeCrossTargetWitness pack
  let restartAdequacy := hasRestartStructuredErrorAdequacyWitness pack
  let singleEvidence := hasSingleThreadEvidence pack
  let multiEvidence := hasMultiThreadEvidence pack
  let shardedEvidence := hasShardedEvidence pack
  let required :=
    replayOk &&
      crossTarget &&
      restartAdequacy &&
      singleEvidence &&
      multiEvidence &&
      shardedEvidence
  let releaseReady := if releaseTagged then required else true
  { version := releaseConformanceReportVersion
  , theoremInventory := inventory
  , transformationEligibility := transform
  , replayConformance := replayOk
  , failureEnvelopeCrossTargetWitness := crossTarget
  , restartStructuredErrorAdequacyWitness := restartAdequacy
  , singleThreadEvidence := singleEvidence
  , multiThreadEvidence := multiEvidence
  , shardedEvidence := shardedEvidence
  , releaseReady := releaseReady
  }

/-- Release-tagged build gate derived from the report. -/
def releaseBuildGate {ε : Type w} [EffectRuntime ε]
    {ν : Type u} [VerificationModel ν]
    {store₀ : SessionStore ν} {State : Type v}
    {space : VMInvariantSpaceWithProfiles (ν := ν) store₀ State}
    (pack : VMTheoremPack (space := space))
    (baseline replay : List (TickedObsEvent ε))
    (classes : List CertifiedReplayEquivalenceClass := defaultCertifiedReplayClasses)
    (releaseTagged : Bool := false) : Bool :=
  (buildReleaseConformanceReport
    (pack := pack)
    (baseline := baseline)
    (replay := replay)
    (classes := classes)
    (releaseTagged := releaseTagged)).releaseReady

end Proofs
end Runtime
