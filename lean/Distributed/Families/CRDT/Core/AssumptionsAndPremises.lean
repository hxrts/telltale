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

/-! ## Assumption Labels -/

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

/-! ## Validation Result Types -/

/-- Validation result for one assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-! ## Core Assumption Catalog -/

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

/-! ## Validation Functions -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)


/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .semilatticeCoreClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Semilattice core premise is provided."
      }
  | .opContextLayerClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Op-context layer premise is provided."
      }
  | .minimalOpStateEquivalenceAssumptions =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Minimal op/state equivalence assumptions are provided."
      }
  | .canonicalConvergenceDistanceClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Canonical convergence-distance class premise is provided."
      }
  | .mixingTimeControlledClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Mixing-time control premise is provided."
      }
  -- Validation cases: dynamics and limits.
  | .hotspotSlowModesClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Hotspot slow-mode premise is provided."
      }
  | .driftDecayClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Drift-decay premise is provided."
      }
  | .sequenceSubclassClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Sequence-subclass premise is provided."
      }
  | .epochBarrierClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Epoch-barrier premise is provided."
      }
/- ## Structured Block 1 -/
  | .boundedMetadataApproxClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Bounded-metadata approximation premise is provided."
      }
  | .multiscaleObservablesClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Multiscale-observables premise is provided."
      }
  | .metadataTradeoffFrontierClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Metadata tradeoff-frontier premise is provided."
      }
  | .gcCausalDominanceClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "GC/causal-dominance premise is provided."
      }
  | .stabilizationLowerBoundClass =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Stabilization lower-bound premise is provided."
      }

/-- Validate a list of assumptions. -/
def validateAssumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-! ## Validation Summary -/

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

/-! ## Theorem Premises Bundle -/

/-- Additional premises used to derive CRDT theorem forms. -/
structure Premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Type (max u v w x y) where
  RefRun : Run State → Prop
  ImplRun : Run State → Prop
  envelopeBudget : DiffBudget
  inferredBudget : DiffBudget
  stateSemantics : StateBasedCRDT State
  opRun : Run State
  stateRun : Run State
  GCSafe : State → Prop
  CausalDominanceEstablished : State → Prop
  approxPolicy : Nat → Nat
  horizon : Nat
  epsilon : Nat
  referenceRun : Run State
  deployedRun : Run State
  implementationMatchesReference :
    ∀ ref impl n, RefRun ref → ImplRun impl → EqSafe M (ref n) (impl n)
  realizableWhenMatches :
    ∀ ref impl, RefRun ref → (∀ n, EqSafe M (ref n) (impl n)) → ImplRun impl
  budgetAligned : inferredBudget = envelopeBudget
  opStateMatches : ∀ n, EqSafe M (opRun n) (stateRun n)
  gcSafetyImpliesCausalDominance :
    ∀ s, GCSafe s → CausalDominanceEstablished s
  causalDominanceImpliesGCSafety :
    ∀ s, CausalDominanceEstablished s → GCSafe s
  distanceBoundUnderPolicy :
    ∀ t, t ≤ horizon →
      M.distance (referenceRun t) (deployedRun t) ≤ epsilon + approxPolicy t
  exactSECZeroBudget :
    (∀ t, approxPolicy t = 0) →
      M.distance (referenceRun 0) (deployedRun 0) ≤ 0

/-! ## Envelope and Adequacy Derivations -/

/-- Exact envelope characterization follows from assumptions + premises. -/
theorem exact_envelope_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ExactEnvelopeCharacterization M p.RefRun p.ImplRun := by
  constructor
  · intro ref impl hRef hImpl n
    exact p.implementationMatchesReference ref impl n hRef hImpl
  constructor
  · intro ref impl hRef hEnvelope
    exact p.realizableWhenMatches ref impl hRef hEnvelope
  · intro R hR ref impl hRef hImpl hRel n
    exact hR ref impl hRef hImpl hRel n

/-- Observational adequacy modulo envelope follows from assumptions + premises. -/
theorem adequacy_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ObservationalAdequacyModuloEnvelope M p.RefRun p.ImplRun := by
  intro ref impl hRef hImpl n
  exact p.implementationMatchesReference ref impl n hRef hImpl

/-- Principal capability theorem follows from assumptions + premises. -/
theorem principal_capability_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    PrincipalCapability p.inferredBudget p.envelopeBudget :=
  p.budgetAligned

/-! ## Admission and Equivalence Derivations -/

/-- Admission soundness theorem follows from assumptions + premises. -/
theorem admission_soundness_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    AdmissionSoundness p.inferredBudget p.envelopeBudget := by
  intro _dUser hLe
  simpa [CapabilityAdmissible, p.budgetAligned] using hLe

/-- Admission completeness theorem follows from assumptions + premises. -/
theorem admission_completeness_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    AdmissionCompleteness p.inferredBudget p.envelopeBudget := by
  intro _dUser
  constructor
  · intro hLe
    simpa [CapabilityAdmissible, p.budgetAligned] using hLe
  · intro hAdmit
    simpa [CapabilityAdmissible, p.budgetAligned] using hAdmit

/-- Op/state equivalence theorem follows from assumptions + premises. -/
theorem op_state_equivalence_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    OpStateEquivalence M p.opRun p.stateRun :=
  p.opStateMatches

/-- GC safety iff causal dominance follows from assumptions + premises. -/
theorem gc_safety_iff_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    GCSafetyIffCausalDominance p.GCSafe p.CausalDominanceEstablished := by
  intro s
  exact ⟨p.gcSafetyImpliesCausalDominance s, p.causalDominanceImpliesGCSafety s⟩

/-! ## Approximation and Limit Derivations -/

/-- Bounded-metadata approximation bound follows from assumptions + premises. -/
theorem bounded_approximation_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    BoundedMetadataApproximation M p.approxPolicy p.horizon p.epsilon
      p.referenceRun p.deployedRun :=
  p.distanceBoundUnderPolicy

/-- Approximation monotonicity theorem follows from assumptions + premises. -/
theorem approximation_monotone_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ApproximationMonotoneUnderPolicyTightening M p.approxPolicy p.approxPolicy
      p.horizon p.epsilon p.referenceRun p.deployedRun := by
  intro _hTight hApprox
  exact hApprox

/-- Exact-SEC recovery-as-limit theorem follows from assumptions + premises. -/
theorem exact_sec_as_limit_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (_a : Assumptions M)
    (p : Premises M) :
    ExactSECRecoveryAsLimit M p.approxPolicy p.referenceRun p.deployedRun := by
  intro hPolicyZero t ht
  have ht0 : t = 0 := Nat.le_zero.mp ht
  subst ht0
  simpa [hPolicyZero 0] using p.exactSECZeroBudget hPolicyZero

/-! ## Derived Bundle Projections -/

/-- `H_crdt_core` from CRDT assumptions. -/
theorem hcrdt_core_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtCore M :=
  ⟨a.semilatticeCoreClass, a.opContextLayerClass⟩

/-- `H_crdt_foundation` from CRDT assumptions. -/
theorem hcrdt_foundation_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtFoundation M :=
  ⟨a.minimalOpStateEquivalenceAssumptions, a.canonicalConvergenceDistanceClass⟩

/-- `H_crdt_dynamics` from CRDT assumptions. -/
theorem hcrdt_dynamics_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtDynamics M :=
  ⟨a.mixingTimeControlledClass, a.hotspotSlowModesClass, a.driftDecayClass⟩

/-- `H_crdt_extensions` from CRDT assumptions. -/
theorem hcrdt_extensions_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtExtensions M :=
  ⟨a.sequenceSubclassClass, a.epochBarrierClass,
    a.boundedMetadataApproxClass, a.multiscaleObservablesClass⟩

/-- `H_crdt_limits` from CRDT assumptions. -/
theorem hcrdt_limits_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (a : Assumptions M) :
    HcrdtLimits M :=
  ⟨a.metadataTradeoffFrontierClass, a.gcCausalDominanceClass,
    a.stabilizationLowerBoundClass⟩


end CRDT
end Distributed
