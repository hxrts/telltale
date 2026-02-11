import Distributed.Families.CRDT.Core.ExtensionsAndLimits

/-! # CRDT Assumptions and Premises

Bundled assumption records and validation infrastructure for CRDT model
verification. Provides structured access to the 14 core model class
predicates required for convergence and envelope theorems. -/

/-
The Problem. CRDT convergence proofs require checking multiple assumption
classes (semilattice core, op-context layer, distance bounds, etc.). Each
theorem lists its prerequisites individually, making assumption tracking
error-prone and validation verbose.

Solution Structure. Bundle assumptions into `Assumptions` record. Provide
`Assumption` enumeration for programmatic validation. Define `coreAssumptions`
list and `AssumptionResult` for structured validation reporting.
-/

set_option autoImplicit false

namespace Distributed
namespace CRDT

universe u v w x y z

/-! ## Assumption Bundle -/

structure Assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop where
  semilatticeCoreClass : M.semilatticeCoreClass
  opContextLayerClass : M.opContextLayerClass
  minimalOpStateEquivalenceAssumptions : M.minimalOpStateEquivalenceAssumptions
  canonicalConvergenceDistanceClass : M.canonicalConvergenceDistanceClass
  mixingTimeControlledClass : M.mixingTimeControlledClass
  hotspotSlowModesClass : M.hotspotSlowModesClass
  driftDecayClass : M.driftDecayClass
  sequenceSubclassClass : M.sequenceSubclassClass
  epochBarrierClass : M.epochBarrierClass
  boundedMetadataApproxClass : M.boundedMetadataApproxClass
  multiscaleObservablesClass : M.multiscaleObservablesClass
  metadataTradeoffFrontierClass : M.metadataTradeoffFrontierClass
  gcCausalDominanceClass : M.gcCausalDominanceClass
  stabilizationLowerBoundClass : M.stabilizationLowerBoundClass

/-- Built-in assumption labels for summary/validation APIs. -/
inductive Assumption where
  | semilatticeCoreClass
  | opContextLayerClass
  | minimalOpStateEquivalenceAssumptions
  | canonicalConvergenceDistanceClass
  | mixingTimeControlledClass
  | hotspotSlowModesClass
  | driftDecayClass
  | sequenceSubclassClass
  | epochBarrierClass
  | boundedMetadataApproxClass
  | multiscaleObservablesClass
  | metadataTradeoffFrontierClass
  | gcCausalDominanceClass
  | stabilizationLowerBoundClass
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable CRDT assumption set. -/
def coreAssumptions : List Assumption :=
  [ .semilatticeCoreClass
  , .opContextLayerClass
  , .minimalOpStateEquivalenceAssumptions
  , .canonicalConvergenceDistanceClass
  , .mixingTimeControlledClass
  , .hotspotSlowModesClass
  , .driftDecayClass
  , .sequenceSubclassClass
  , .epochBarrierClass
  , .boundedMetadataApproxClass
  , .multiscaleObservablesClass
  , .metadataTradeoffFrontierClass
  , .gcCausalDominanceClass
  , .stabilizationLowerBoundClass
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .semilatticeCoreClass =>
      { assumption := h
      , passed := true
      , detail := "Semilattice core premise is provided."
      }
  | .opContextLayerClass =>
      { assumption := h
      , passed := true
      , detail := "Op-context layer premise is provided."
      }
  | .minimalOpStateEquivalenceAssumptions =>
      { assumption := h
      , passed := true
      , detail := "Minimal op/state equivalence assumptions are provided."
      }
  | .canonicalConvergenceDistanceClass =>
      { assumption := h
      , passed := true
      , detail := "Canonical convergence-distance class premise is provided."
      }
  | .mixingTimeControlledClass =>
      { assumption := h
      , passed := true
      , detail := "Mixing-time control premise is provided."
      }
  | .hotspotSlowModesClass =>
      { assumption := h
      , passed := true
      , detail := "Hotspot slow-mode premise is provided."
      }
  | .driftDecayClass =>
      { assumption := h
      , passed := true
      , detail := "Drift-decay premise is provided."
      }
  | .sequenceSubclassClass =>
      { assumption := h
      , passed := true
      , detail := "Sequence-subclass premise is provided."
      }
  | .epochBarrierClass =>
      { assumption := h
      , passed := true
      , detail := "Epoch-barrier premise is provided."
      }
  | .boundedMetadataApproxClass =>
      { assumption := h
      , passed := true
      , detail := "Bounded-metadata approximation premise is provided."
      }
  | .multiscaleObservablesClass =>
      { assumption := h
      , passed := true
      , detail := "Multiscale-observables premise is provided."
      }
  | .metadataTradeoffFrontierClass =>
      { assumption := h
      , passed := true
      , detail := "Metadata tradeoff-frontier premise is provided."
      }
  | .gcCausalDominanceClass =>
      { assumption := h
      , passed := true
      , detail := "GC/causal-dominance premise is provided."
      }
  | .stabilizationLowerBoundClass =>
      { assumption := h
      , passed := true
      , detail := "Stabilization lower-bound premise is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) (hs : List Assumption) : AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-- Additional premises used to derive CRDT theorem forms. -/
structure Premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Type (max u v w x y) where
  RefRun : Run State → Prop
  ImplRun : Run State → Prop
  envelopeBudget : DiffBudget
  inferredBudget : DiffBudget
  opRun : Run State
  stateRun : Run State
  GCSafe : State → Prop
  CausalDominanceEstablished : State → Prop
  approxPolicy : Nat → Nat
  horizon : Nat
  epsilon : Nat
  referenceRun : Run State
  deployedRun : Run State
  envelopeSoundnessWitness : EnvelopeSoundness M RefRun ImplRun
  envelopeRealizabilityWitness : EnvelopeRealizability M RefRun ImplRun
  envelopeMaximalityWitness : EnvelopeMaximality M RefRun ImplRun
  adequacyWitness : ObservationalAdequacyModuloEnvelope M RefRun ImplRun
  principalCapabilityWitness : PrincipalCapability inferredBudget envelopeBudget
  admissionSoundnessWitness : AdmissionSoundness inferredBudget envelopeBudget
  admissionCompletenessWitness : AdmissionCompleteness inferredBudget envelopeBudget
  opStateEquivalenceWitness : OpStateEquivalence M opRun stateRun
  gcSafetyIffWitness :
    GCSafetyIffCausalDominance GCSafe CausalDominanceEstablished
  boundedApproximationWitness :
    BoundedMetadataApproximation M approxPolicy horizon epsilon referenceRun deployedRun
  approximationMonotoneWitness :
    ApproximationMonotoneUnderPolicyTightening
      M approxPolicy approxPolicy horizon epsilon referenceRun deployedRun
  exactSECAsLimitWitness :
    ExactSECRecoveryAsLimit M approxPolicy referenceRun deployedRun

/-- Exact envelope characterization follows from assumptions + premises. -/
theorem exactEnvelope_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ExactEnvelopeCharacterization M p.RefRun p.ImplRun := by
  exact ⟨p.envelopeSoundnessWitness, p.envelopeRealizabilityWitness, p.envelopeMaximalityWitness⟩

/-- Observational adequacy modulo envelope follows from assumptions + premises. -/
theorem adequacy_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ObservationalAdequacyModuloEnvelope M p.RefRun p.ImplRun :=
  p.adequacyWitness

/-- Principal capability theorem follows from assumptions + premises. -/
theorem principalCapability_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    PrincipalCapability p.inferredBudget p.envelopeBudget :=
  p.principalCapabilityWitness

/-- Admission soundness theorem follows from assumptions + premises. -/
theorem admissionSoundness_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    AdmissionSoundness p.inferredBudget p.envelopeBudget :=
  p.admissionSoundnessWitness

/-- Admission completeness theorem follows from assumptions + premises. -/
theorem admissionCompleteness_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    AdmissionCompleteness p.inferredBudget p.envelopeBudget :=
  p.admissionCompletenessWitness

/-- Op/state equivalence theorem follows from assumptions + premises. -/
theorem opStateEquivalence_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    OpStateEquivalence M p.opRun p.stateRun :=
  p.opStateEquivalenceWitness

/-- GC safety iff causal dominance follows from assumptions + premises. -/
theorem gcSafetyIff_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    GCSafetyIffCausalDominance p.GCSafe p.CausalDominanceEstablished :=
  p.gcSafetyIffWitness

/-- Bounded-metadata approximation bound follows from assumptions + premises. -/
theorem boundedApproximation_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    BoundedMetadataApproximation M p.approxPolicy p.horizon p.epsilon
      p.referenceRun p.deployedRun :=
  p.boundedApproximationWitness

/-- Approximation monotonicity theorem follows from assumptions + premises. -/
theorem approximationMonotone_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ApproximationMonotoneUnderPolicyTightening M p.approxPolicy p.approxPolicy
      p.horizon p.epsilon p.referenceRun p.deployedRun :=
  p.approximationMonotoneWitness

/-- Exact-SEC recovery-as-limit theorem follows from assumptions + premises. -/
theorem exactSECAsLimit_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ExactSECRecoveryAsLimit M p.approxPolicy p.referenceRun p.deployedRun :=
  p.exactSECAsLimitWitness

/-- `H_crdt_core` from CRDT assumptions. -/
theorem hcrdtCore_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtCore M :=
  ⟨a.semilatticeCoreClass, a.opContextLayerClass⟩

/-- `H_crdt_foundation` from CRDT assumptions. -/
theorem hcrdtFoundation_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtFoundation M :=
  ⟨a.minimalOpStateEquivalenceAssumptions, a.canonicalConvergenceDistanceClass⟩

/-- `H_crdt_dynamics` from CRDT assumptions. -/
theorem hcrdtDynamics_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtDynamics M :=
  ⟨a.mixingTimeControlledClass, a.hotspotSlowModesClass, a.driftDecayClass⟩

/-- `H_crdt_extensions` from CRDT assumptions. -/
theorem hcrdtExtensions_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtExtensions M :=
  ⟨a.sequenceSubclassClass, a.epochBarrierClass,
    a.boundedMetadataApproxClass, a.multiscaleObservablesClass⟩

/-- `H_crdt_limits` from CRDT assumptions. -/
theorem hcrdtLimits_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtLimits M :=
  ⟨a.metadataTradeoffFrontierClass, a.gcCausalDominanceClass,
    a.stabilizationLowerBoundClass⟩


end CRDT
end Distributed
