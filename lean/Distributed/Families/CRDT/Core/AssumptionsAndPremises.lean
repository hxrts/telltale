import Distributed.Families.CRDT.Core.ExtensionsAndLimits

/-! # CRDT Premises

Premise bundle for CRDT envelope/budget theorem forms over abstract run sets.
The algebraic CRDT laws are not premises: they live in `Model.lattice` and are
proved in `Semilattice`/`CoreModel`. The former fourteen free `Prop` class tags
and their constant-`true` validator were removed because they constrained nothing.
Adequacy over abstract `RefRun`/`ImplRun` remains conditional
(`adequacy_of_refinement_hypothesis`); for step-relation models it is proved in
`Distributed.Families.CRDT.Core.Adequacy`. -/

set_option autoImplicit false

namespace Distributed
namespace CRDT

universe u v w x y z

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
  /-- Refinement hypothesis (not derived from the CRDT model). -/
  refinementHypothesis :
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
    (p : Premises M) :
    ExactEnvelopeCharacterization M p.RefRun p.ImplRun := by
  constructor
  · intro ref impl hRef hImpl n
    exact p.refinementHypothesis ref impl n hRef hImpl
  constructor
  · intro ref impl hRef hEnvelope
    exact p.realizableWhenMatches ref impl hRef hEnvelope
  · intro R hR ref impl hRef hImpl hRel n
    exact hR ref impl hRef hImpl hRel n

/-- Conditional adequacy: restates the premise `refinementHypothesis`; the CRDT
model has no step semantics from which it could be proved. -/
theorem adequacy_of_refinement_hypothesis
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    ObservationalAdequacyModuloEnvelope M p.RefRun p.ImplRun := by
  intro ref impl hRef hImpl n
  exact p.refinementHypothesis ref impl n hRef hImpl

/-- Principal capability theorem follows from assumptions + premises. -/
theorem principal_capability_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    PrincipalCapability p.inferredBudget p.envelopeBudget :=
  p.budgetAligned

/-! ## Admission and Equivalence Derivations -/

/-- Admission soundness theorem follows from assumptions + premises. -/
theorem admission_soundness_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    AdmissionSoundness p.inferredBudget p.envelopeBudget := by
  intro _dUser hLe
  simpa [CapabilityAdmissible, p.budgetAligned] using hLe

/-- Admission completeness theorem follows from assumptions + premises. -/
theorem admission_completeness_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
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
    (p : Premises M) :
    OpStateEquivalence M p.opRun p.stateRun :=
  p.opStateMatches

/-- GC safety iff causal dominance follows from assumptions + premises. -/
theorem gc_safety_iff_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    GCSafetyIffCausalDominance p.GCSafe p.CausalDominanceEstablished := by
  intro s
  exact ⟨p.gcSafetyImpliesCausalDominance s, p.causalDominanceImpliesGCSafety s⟩

/-! ## Approximation and Limit Derivations -/

/-- Bounded-metadata approximation bound follows from assumptions + premises. -/
theorem bounded_approximation_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    BoundedMetadataApproximation M p.approxPolicy p.horizon p.epsilon
      p.referenceRun p.deployedRun :=
  p.distanceBoundUnderPolicy

/-- Approximation monotonicity theorem follows from assumptions + premises. -/
theorem approximation_monotone_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    ApproximationMonotoneUnderPolicyTightening M p.approxPolicy p.approxPolicy
      p.horizon p.epsilon p.referenceRun p.deployedRun := by
  intro _hTight hApprox
  exact hApprox

/-- Exact-SEC recovery-as-limit theorem follows from assumptions + premises. -/
theorem exact_sec_as_limit_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    ExactSECRecoveryAsLimit M p.approxPolicy p.referenceRun p.deployedRun := by
  intro hPolicyZero t ht
  have ht0 : t = 0 := Nat.le_zero.mp ht
  subst ht0
  simpa [hPolicyZero 0] using p.exactSECZeroBudget hPolicyZero

end CRDT
end Distributed
