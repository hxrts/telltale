import Distributed.Families.CRDT.Core.FamilyDynamics

/-! # CRDT Extensions and Limits

Higher-level CRDT extension predicates, counterexamples, and limit models
for testing assumption boundaries. -/

/-
The Problem. CRDT models have extension predicates (sequence subclass,
epoch barriers, bounded approximation) that combine base model classes.
We need both positive examples (models satisfying extensions) and negative
examples (counterexamples violating specific conditions) for testing.

Solution Structure. Define `HcrdtExtensions` predicate bundling common
extension classes. Provide counterexample functions (`sequenceIdIssuerConstant`,
`recycledActorRun`) and structured-state test models for validation.
-/

set_option autoImplicit false

namespace Distributed
namespace CRDT

universe u v w x y z

/-! ## Extension Predicates -/

def HcrdtExtensions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.sequenceSubclassClass ∧ M.epochBarrierClass ∧
  M.boundedMetadataApproxClass ∧ M.multiscaleObservablesClass

/-- Sequence-identifier subclass criterion (strict monotonicity of issued ids). -/
def SequenceIdSubclassCriterion (issueId : Nat → Nat) : Prop :=
  ∀ ⦃i j : Nat⦄, i < j → issueId i < issueId j

/-- Actor-id recycling safety condition over a run of issued actor ids. -/
def ActorIdRecyclingSafeRun (ids : Run Nat) : Prop :=
  ∀ t, ids (t + 1) ≠ ids t

/-- Approximation-envelope semantics: zero distance implies safety-visible equality. -/
theorem boundedApproximation_zeroBudget_implies_envelope
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (hZeroDistanceSafe : ∀ s₁ s₂, M.distance s₁ s₂ = 0 → EqSafe M s₁ s₂)
    (T : Nat)
    (ref impl : Run State)
    (hApprox : BoundedMetadataApproximation M (fun _ => 0) T 0 ref impl) :
    ∀ t, t ≤ T → EqSafe M (ref t) (impl t) := by
  intro t ht
  have hDist : M.distance (ref t) (impl t) ≤ 0 := by
    simpa using hApprox t ht
  have hEqZero : M.distance (ref t) (impl t) = 0 :=
    Nat.le_zero.mp hDist
  exact hZeroDistanceSafe (ref t) (impl t) hEqZero

/-- Counterexample id issuer violating sequence subclass criterion. -/
def sequenceIdIssuerConstant : Nat → Nat :=
  fun _ => 0

/-- Counterexample actor-id run violating recycling safety. -/
def recycledActorRun : Run Nat :=
  fun _ => 7

/-- Structured-state model with single-scale observable projection. -/
def structuredSingleScaleModel : Model (Nat × Nat) Unit Unit Nat Unit where
  observe := Prod.fst
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := True
  mixingTimeControlledClass := True
  hotspotSlowModesClass := True
  driftDecayClass := True
  sequenceSubclassClass := True
  epochBarrierClass := True
  boundedMetadataApproxClass := True
  multiscaleObservablesClass := False
  metadataTradeoffFrontierClass := True
  gcCausalDominanceClass := True
  stabilizationLowerBoundClass := True

/-- Structured-state model with multi-scale observable projection. -/
def structuredMultiScaleModel : Model (Nat × Nat) Unit Unit (Nat × Nat) Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := True
  mixingTimeControlledClass := True
  hotspotSlowModesClass := True
  driftDecayClass := True
  sequenceSubclassClass := True
  epochBarrierClass := True
  boundedMetadataApproxClass := True
  multiscaleObservablesClass := True
  metadataTradeoffFrontierClass := True
  gcCausalDominanceClass := True
  stabilizationLowerBoundClass := True

/-- Constant id issue stream refutes strict sequence-subclass criteria. -/
theorem sequenceIdCriterion_counterexample :
    ¬ SequenceIdSubclassCriterion sequenceIdIssuerConstant := by
  intro hMono
  have hLt : sequenceIdIssuerConstant 0 < sequenceIdIssuerConstant 1 :=
    hMono (by decide : 0 < 1)
  simp [sequenceIdIssuerConstant] at hLt

/-- Constant actor-id stream refutes recycling safety. -/
theorem actorIdRecycling_counterexample :
    ¬ ActorIdRecyclingSafeRun recycledActorRun := by
  intro hSafe
  exact hSafe 0 (by simp [recycledActorRun])

/-- Single-scale observables can miss structured differences. -/
theorem singleScale_observables_not_sufficient :
    EqSafe structuredSingleScaleModel (0, 0) (0, 1) := by
  simp [EqSafe, structuredSingleScaleModel]

/-- Multi-scale observables recover the missing structured distinction. -/
theorem multiScale_observables_distinguish :
    ¬ EqSafe structuredMultiScaleModel (0, 0) (0, 1) := by
  simp [EqSafe, structuredMultiScaleModel]

/-- Extension-counterexample bundle for sequence ids, actor recycling, and observability scale. -/
theorem hcrdtExtensions_counterexample_bundle :
    ¬ SequenceIdSubclassCriterion sequenceIdIssuerConstant ∧
      ¬ ActorIdRecyclingSafeRun recycledActorRun ∧
      EqSafe structuredSingleScaleModel (0, 0) (0, 1) ∧
      ¬ EqSafe structuredMultiScaleModel (0, 0) (0, 1) := by
  exact ⟨sequenceIdCriterion_counterexample, actorIdRecycling_counterexample,
    singleScale_observables_not_sufficient, multiScale_observables_distinguish⟩

/-- Hypothesis block matching `H_crdt_limits`. -/
def HcrdtLimits
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.metadataTradeoffFrontierClass ∧ M.gcCausalDominanceClass ∧
  M.stabilizationLowerBoundClass

/-- Metadata policy used to witness a non-exact SEC frontier point. -/
def metadataFrontierPolicy : Nat → Nat :=
  fun t => if t = 0 then 1 else 0

/-- Reference run for metadata-vs-SEC frontier witness. -/
def refRunMetadataFrontier : Run Nat :=
  fun _ => 0

/-- Deployed run for metadata-vs-SEC frontier witness. -/
def implRunMetadataFrontier : Run Nat :=
  fun t => if t = 0 then 1 else 0

/-- Frontier witness: bounded metadata approximation can hold while exact envelope fails. -/
theorem metadataVsSEC_frontier_counterexample :
    BoundedMetadataApproximation natUnitModel metadataFrontierPolicy 0 0
      refRunMetadataFrontier implRunMetadataFrontier ∧
      ¬ Envelope natUnitModel refRunMetadataFrontier implRunMetadataFrontier := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht0 : t = 0 := Nat.le_zero.mp ht
    subst ht0
    simp [natUnitModel, refRunMetadataFrontier,
      implRunMetadataFrontier, metadataFrontierPolicy]
  · intro hEnv
    have h0 : EqSafe natUnitModel (refRunMetadataFrontier 0) (implRunMetadataFrontier 0) := hEnv 0
    have hEq : (0 : Nat) = 1 := by
      simp [EqSafe, natUnitModel, refRunMetadataFrontier, implRunMetadataFrontier] at h0
    exact Nat.zero_ne_one hEq

/-- Simple GC-safety predicate for `Nat` states. -/
def gcSafeZero : Nat → Prop :=
  fun s => s = 0

/-- Causal-dominance predicate matching `gcSafeZero` for the witness model. -/
def causalDominanceZero : Nat → Prop :=
  fun s => s = 0

/-- GC safety iff causal dominance concrete witness. -/
theorem gcSafetyIff_causalDominanceZero :
    GCSafetyIffCausalDominance gcSafeZero causalDominanceZero := by
  intro s
  rfl

/-- Stabilization-delay lower-bound relation parameterized by fairness and churn. -/
def StabilizationDelayTailLowerBound (fairness churn tail : Nat) : Prop :=
  churn - fairness ≤ tail

/-- No-fairness specialization: tail lower bound is at least churn. -/
theorem stabilizationTail_noFairness_lowerBound (churn : Nat) :
    StabilizationDelayTailLowerBound 0 churn churn := by
  simp [StabilizationDelayTailLowerBound]

/-- If churn exceeds fairness, any valid delay tail must be positive. -/
theorem stabilizationTail_positive_when_churn_exceeds_fairness
    {fairness churn tail : Nat}
    (hGap : fairness < churn)
    (hTail : StabilizationDelayTailLowerBound fairness churn tail) :
    0 < tail := by
  have hPos : 0 < churn - fairness := Nat.sub_pos_of_lt hGap
  exact Nat.lt_of_lt_of_le hPos hTail

/-- Existence form of the stabilization-delay lower-bound theorem. -/
theorem stabilizationTail_lowerBound_exists
    {fairness churn : Nat}
    (hGap : fairness < churn) :
    ∃ tail, StabilizationDelayTailLowerBound fairness churn tail ∧ 0 < tail := by
  refine ⟨churn - fairness, Nat.le_refl (churn - fairness), Nat.sub_pos_of_lt hGap⟩

/-- `H_crdt_limits` witness bundle: frontier, GC iff dominance, and churn/fairness lower bound. -/
theorem hcrdtLimits_witness_bundle :
    (BoundedMetadataApproximation natUnitModel metadataFrontierPolicy 0 0
      refRunMetadataFrontier implRunMetadataFrontier ∧
      ¬ Envelope natUnitModel refRunMetadataFrontier implRunMetadataFrontier) ∧
      GCSafetyIffCausalDominance gcSafeZero causalDominanceZero ∧
      (∀ fairness churn, fairness < churn →
        ∃ tail, StabilizationDelayTailLowerBound fairness churn tail ∧ 0 < tail) := by
  refine ⟨metadataVsSEC_frontier_counterexample, gcSafetyIff_causalDominanceZero, ?_⟩
  intro fairness churn hGap
  exact stabilizationTail_lowerBound_exists hGap

end CRDT
end Distributed
