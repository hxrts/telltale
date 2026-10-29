import Distributed.Families.CRDT.Core.ExtensionsAndLimits

/-! # CRDT Premises

Premise bundle for CRDT envelope/budget theorem forms over abstract run sets.
The algebraic CRDT laws are not premises: they live in `Model.lattice` and are
proved in `Semilattice`/`CoreModel`. The former fourteen free `Prop` class tags
and their constant-`true` validator were removed because they constrained nothing.
Adequacy over abstract `RefRun`/`ImplRun` remains conditional
(`adequacy_of_refinement_hypothesis`); for step-relation models it is proved in
`Distributed.Families.CRDT.Core.Adequacy`.

Of the remaining theorem forms:
- op/state equivalence is proved: `opRun`/`stateRun` are defined from an op
  log as op-based delivery and state-based merging, equal by
  `Model.deliver_eq_mergeAll`,
- GC safety iff causal dominance is proved: `GCSafe s` (discarding the
  buffered deltas `gcBuffer` loses nothing) and causal dominance (`s` dominates
  every buffered delta) are defined in the lattice and shown equivalent,
- exact SEC as a limit is proved from the metric law `distanceSelf` and a
  common start `sameStart`,
- the bounded-metadata distance bound is *not* derivable (`distance` is
  uninterpreted); it is the explicitly named assumption
  `assumedDistanceBound`, and `bounded_approximation_of_assumptions` merely
  exposes it. -/

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
  /-- Base state of the op/state comparison. -/
  opBase : State
  /-- Updates delivered by time `n` in the op/state comparison. -/
  opLog : Nat → List Op
  /-- Buffered deltas a garbage collector would discard. -/
  gcBuffer : List State
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
  /-- Explicit assumption (not derived; `distance` is uninterpreted): the
  deployed run stays within `epsilon + approxPolicy t` of the reference. -/
  assumedDistanceBound :
    ∀ t, t ≤ horizon →
      M.distance (referenceRun t) (deployedRun t) ≤ epsilon + approxPolicy t
  /-- Metric law: a state is at distance `0` from itself. -/
  distanceSelf : ∀ s, M.distance s s = 0
  /-- Reference and deployed runs start from the same state. -/
  sameStart : referenceRun 0 = deployedRun 0

variable {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
  {M : Model State Op Context Obs Program}

/-- Op-based run: sequential delivery of the op log. -/
def Premises.opRun (p : Premises M) : Run State := fun n => M.deliver p.opBase (p.opLog n)

/-- State-based run: merging the deltas of the op log. -/
def Premises.stateRun (p : Premises M) : Run State :=
  fun n => mergeAll M.lattice p.opBase ((p.opLog n).map M.effect)

/-- GC safety: merging the buffered deltas back changes nothing. -/
def Premises.GCSafe (p : Premises M) (s : State) : Prop :=
  mergeAll M.lattice s p.gcBuffer = s

/-- Causal dominance: `s` dominates every buffered delta. -/
def Premises.CausalDominanceEstablished (p : Premises M) (s : State) : Prop :=
  ∀ x ∈ p.gcBuffer, M.lattice.le x s

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

/-- Op/state equivalence, proved: op delivery is merging deltas. -/
theorem op_state_equivalence_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    OpStateEquivalence M p.opRun p.stateRun :=
  fun n => congrArg M.observe (M.deliver_eq_mergeAll (p.opLog n) p.opBase)

/-- GC safety iff causal dominance, proved from the lub characterization of
`mergeAll` and antisymmetry. -/
theorem gc_safety_iff_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    GCSafetyIffCausalDominance p.GCSafe p.CausalDominanceEstablished := by
  intro s
  have hUb := (mergeAll_le_iff M.lattice p.gcBuffer s _).1 (M.lattice.le_refl _)
  constructor
  · intro h x hx
    have := hUb.2 x hx
    unfold Premises.GCSafe at h
    rwa [h] at this
  · intro h
    exact M.lattice.le_antisymm
      ((mergeAll_le_iff M.lattice p.gcBuffer s s).2 ⟨M.lattice.le_refl s, h⟩) hUb.1

/-! ## Approximation and Limit Derivations -/

/-- Bounded-metadata approximation: exposes the named assumption
`assumedDistanceBound` (not derived). -/
theorem bounded_approximation_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    BoundedMetadataApproximation M p.approxPolicy p.horizon p.epsilon
      p.referenceRun p.deployedRun :=
  p.assumedDistanceBound

/-- Approximation monotonicity theorem follows from assumptions + premises. -/
theorem approximation_monotone_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    ApproximationMonotoneUnderPolicyTightening M p.approxPolicy p.approxPolicy
      p.horizon p.epsilon p.referenceRun p.deployedRun := by
  intro _hTight hApprox
  exact hApprox

/-- Exact SEC as a limit, proved from `distanceSelf` and `sameStart`. -/
theorem exact_sec_as_limit_of_assumptions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    (p : Premises M) :
    ExactSECRecoveryAsLimit M p.approxPolicy p.referenceRun p.deployedRun := by
  intro hPolicyZero t ht
  have ht0 : t = 0 := Nat.le_zero.mp ht
  subst ht0
  rw [p.sameStart, p.distanceSelf]
  exact Nat.zero_le _

end CRDT
end Distributed
