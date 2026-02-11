set_option autoImplicit false

/-! # Distributed.Families.CRDT

Reusable CRDT theorem-family infrastructure:
- exact envelope characterization,
- observational adequacy modulo envelope,
- principal capability/admission claims,
- op/state equivalence,
- GC safety and bounded-approximation claims,
- CRDT hypothesis bundles from the research plan.
-/

/-
The Problem. We need one reusable distributed-family module for CRDT theorem forms
that can be attached to VM theorem packs, instead of keeping CRDT claims as prose only.
Solution Structure. Define a minimal CRDT model interface and proposition families,
then expose assumption bundles, validation helpers, and protocol-level API wrappers.
-/

/-! ## Core Development -/

namespace Distributed
namespace CRDT

universe u v w x y z

/-- Minimal model interface for CRDT-envelope and equivalence reasoning. -/
structure Model
    (State : Type u)
    (Op : Type v)
    (Context : Type w)
    (Obs : Type x)
    (Program : Type y) where
  observe : State → Obs
  distance : State → State → Nat
  semilatticeCoreClass : Prop
  opContextLayerClass : Prop
  minimalOpStateEquivalenceAssumptions : Prop
  canonicalConvergenceDistanceClass : Prop
  mixingTimeControlledClass : Prop
  hotspotSlowModesClass : Prop
  driftDecayClass : Prop
  sequenceSubclassClass : Prop
  epochBarrierClass : Prop
  boundedMetadataApproxClass : Prop
  multiscaleObservablesClass : Prop
  metadataTradeoffFrontierClass : Prop
  gcCausalDominanceClass : Prop
  stabilizationLowerBoundClass : Prop

/-- Canonical run type used in CRDT envelope statements. -/
abbrev Run (State : Type u) := Nat → State

/-- Safety-visible observational equivalence for CRDT states. -/
def EqSafe
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) (s₁ s₂ : State) : Prop :=
  M.observe s₁ = M.observe s₂

/-- Envelope relation for one reference/deployed run pair. -/
def Envelope
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (ref impl : Run State) : Prop :=
  ∀ n, EqSafe M (ref n) (impl n)

/-- Soundness half: admitted implementations stay inside the CRDT envelope. -/
def EnvelopeSoundness
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → ImplRun impl → Envelope M ref impl

/-- Realizability/completeness half: every envelope-admitted diff is realizable. -/
def EnvelopeRealizability
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → Envelope M ref impl → ImplRun impl

/-- Relative maximality for an envelope relation under fixed model assumptions. -/
def EnvelopeMaximality
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ R : Run State → Run State → Prop,
    (∀ ref impl, RefRun ref → ImplRun impl → R ref impl →
      ∀ n, EqSafe M (ref n) (impl n)) →
      (∀ ref impl, RefRun ref → ImplRun impl → R ref impl → Envelope M ref impl)

/-- Exact characterization theorem form for `Envelope_crdt`. -/
def ExactEnvelopeCharacterization
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  EnvelopeSoundness M RefRun ImplRun ∧
  EnvelopeRealizability M RefRun ImplRun ∧
  EnvelopeMaximality M RefRun ImplRun

/-- Abstract-vs-runtime adequacy modulo the CRDT envelope. -/
def ObservationalAdequacyModuloEnvelope
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RefRun ImplRun : Run State → Prop) : Prop :=
  ∀ ref impl, RefRun ref → ImplRun impl → Envelope M ref impl

/-- Capability budget domain (coarse but decidable). -/
abbrev DiffBudget := Nat

/-- Admissibility relation induced by an envelope budget. -/
def CapabilityAdmissible (envelopeBudget : DiffBudget) (d : DiffBudget) : Prop :=
  d ≤ envelopeBudget

/-- Principal-capability theorem form. -/
def PrincipalCapability
    (dProg envelopeBudget : DiffBudget) : Prop :=
  dProg = envelopeBudget

/-- Admission soundness theorem form. -/
def AdmissionSoundness
    (dProg envelopeBudget : DiffBudget) : Prop :=
  ∀ dUser, dUser ≤ dProg → CapabilityAdmissible envelopeBudget dUser

/-- Admission completeness theorem form. -/
def AdmissionCompleteness
    (dProg envelopeBudget : DiffBudget) : Prop :=
  ∀ dUser, dUser ≤ dProg ↔ CapabilityAdmissible envelopeBudget dUser

/-- Op-vs-state semantics equivalence theorem form. -/
def OpStateEquivalence
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (opRun stateRun : Run State) : Prop :=
  ∀ n, EqSafe M (opRun n) (stateRun n)

/-- GC safety iff causal-dominance theorem form. -/
def GCSafetyIffCausalDominance
    {State : Type u}
    (GCSafe CausalDominanceEstablished : State → Prop) : Prop :=
  ∀ s, GCSafe s ↔ CausalDominanceEstablished s

/-- Bounded-metadata approximation relation between runs. -/
def BoundedMetadataApproximation
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (policy : Nat → Nat)
    (T ε : Nat)
    (ref impl : Run State) : Prop :=
  ∀ t, t ≤ T → M.distance (ref t) (impl t) ≤ ε + policy t

/-- Approximation error monotonicity under policy tightening. -/
def ApproximationMonotoneUnderPolicyTightening
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (tight loose : Nat → Nat)
    (T ε : Nat)
    (ref impl : Run State) : Prop :=
  (∀ t, tight t ≤ loose t) →
    BoundedMetadataApproximation M tight T ε ref impl →
      BoundedMetadataApproximation M loose T ε ref impl

/-- Exact-SEC recovery condition as a limit/special case. -/
def ExactSECRecoveryAsLimit
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (policy : Nat → Nat)
    (ref impl : Run State) : Prop :=
  (∀ t, policy t = 0) → BoundedMetadataApproximation M policy 0 0 ref impl

/-- First-order serializable core continuation payload (`OpCore`). -/
structure OpCore (OpTag : Type v) (Args : Type w) where
  opTag : OpTag
  args : Args
  deriving Repr, DecidableEq, Inhabited

/-- Deterministic interpreter for `OpCore` continuations. -/
structure OpCoreInterpreter
    (State : Type u) (Context : Type v) (OpTag : Type w) (Args : Type x) where
  causalGuard : Context → OpTag → Args → Bool
  delta : OpTag → Args → State → State

/-- Core evaluator: guard-checked deterministic state transformer. -/
def evalCore
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (k : OpCore OpTag Args) (ctx : Context) (s : State) : State :=
  if interp.causalGuard ctx k.opTag k.args then
    interp.delta k.opTag k.args s
  else
    s

/-- Determinism of `evalCore` (functionality/uniqueness of result). -/
theorem evalCore_deterministic
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (k : OpCore OpTag Args) (ctx : Context) (s out₁ out₂ : State)
    (h₁ : evalCore interp k ctx s = out₁)
    (h₂ : evalCore interp k ctx s = out₂) :
    out₁ = out₂ := by
  simpa [h₁] using h₂

/-- Replay stability for `evalCore`: re-applying the same step is idempotent. -/
def ReplayStableCoreEval
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args) : Prop :=
  ∀ k ctx s, evalCore interp k ctx (evalCore interp k ctx s) = evalCore interp k ctx s

/-- Idempotence condition for interpreter deltas. -/
def DeltaIdempotent
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args) : Prop :=
  ∀ tag args s, interp.delta tag args (interp.delta tag args s) = interp.delta tag args s

/-- `evalCore` replay stability follows when `delta` is idempotent. -/
theorem replayStable_of_deltaIdempotent
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (hIdem : DeltaIdempotent interp) :
    ReplayStableCoreEval interp := by
  intro k ctx s
  unfold evalCore
  by_cases h : interp.causalGuard ctx k.opTag k.args
  · simpa [h] using hIdem k.opTag k.args s
  · simp [h]

/-- Serialization roundtrip property for transport-stable `OpCore` payloads. -/
def SerializationRoundTrip
    {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (encode : OpCore OpTag Args → Enc)
    (decode : Enc → Option (OpCore OpTag Args)) : Prop :=
  ∀ k, decode (encode k) = some k

/-- Transport-serialization invariance witness for `OpCore` payloads. -/
def TransportSerializationInvariant
    {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (encode : OpCore OpTag Args → Enc)
    (decode : Enc → Option (OpCore OpTag Args)) : Prop :=
  SerializationRoundTrip encode decode

/-- Roundtrip serialization immediately yields transport-serialization invariance. -/
theorem transportSerializationInvariant_of_roundTrip
    {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (encode : OpCore OpTag Args → Enc)
    (decode : Enc → Option (OpCore OpTag Args))
    (hRoundTrip : SerializationRoundTrip encode decode) :
    TransportSerializationInvariant encode decode :=
  hRoundTrip

/-- Evaluator variant without causal-guard checking (used for boundary counterexamples). -/
def evalCoreNoGuard
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (k : OpCore OpTag Args) (_ctx : Context) (s : State) : State :=
  interp.delta k.opTag k.args s

/-- Simple concrete CRDT model used for OpCore boundary counterexamples. -/
def natUnitModel : Model Nat Unit Unit Nat Unit where
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

/-- Canonical unit operation payload used in counterexamples. -/
def unitOpCore : OpCore Unit Unit :=
  { opTag := (), args := () }

/-- Interpreter where guard rejects an incrementing operation. -/
def interpDeniedIncrement : OpCoreInterpreter Nat Unit Unit Unit where
  causalGuard := fun _ _ _ => false
  delta := fun _ _ s => s + 1

/-- Reference run for the causal-guard counterexample (guarded semantics). -/
def refRunDenied : Run Nat :=
  fun _ => 0

/-- Guardless implementation run that executes the denied operation at tick 0. -/
def implRunNoGuardDenied : Run Nat :=
  fun n => if n = 0 then evalCoreNoGuard interpDeniedIncrement unitOpCore () 0 else 0

/-- Removing `causalGuard` admits an observable envelope violation. -/
theorem envelopeCounterexample_without_causalGuard :
    ¬ Envelope natUnitModel refRunDenied implRunNoGuardDenied := by
  intro hEnv
  have h0 : EqSafe natUnitModel (refRunDenied 0) (implRunNoGuardDenied 0) := hEnv 0
  have hEq : (0 : Nat) = 1 := by
    simp [EqSafe, natUnitModel, refRunDenied, implRunNoGuardDenied, evalCoreNoGuard,
      interpDeniedIncrement, unitOpCore] at h0
  exact Nat.zero_ne_one hEq

/-- Nondeterministic one-step semantics used to witness loss of determinism. -/
def evalCoreNondet (s out : Nat) : Prop :=
  out = s ∨ out = s + 1

/-- Reference run for nondeterminism counterexample. -/
def refRunDetZero : Run Nat :=
  fun _ => 0

/-- One admissible nondeterministic implementation run choosing the divergent branch. -/
def implRunNondetOne : Run Nat :=
  fun n => if n = 0 then 1 else 0

/-- Removing determinism admits distinct outcomes from the same input step. -/
theorem nondeterministic_step_exists_distinct :
    ∃ out₁ out₂, evalCoreNondet 0 out₁ ∧ evalCoreNondet 0 out₂ ∧ out₁ ≠ out₂ := by
  refine ⟨0, 1, ?_, ?_, by decide⟩
  · simp [evalCoreNondet]
  · simp [evalCoreNondet]

/-- Nondeterministic divergent branch violates the envelope against deterministic reference. -/
theorem envelopeCounterexample_without_determinism :
    evalCoreNondet 0 (implRunNondetOne 0) ∧
      ¬ Envelope natUnitModel refRunDetZero implRunNondetOne := by
  refine ⟨?_, ?_⟩
  · simp [evalCoreNondet, implRunNondetOne]
  · intro hEnv
    have h0 : EqSafe natUnitModel (refRunDetZero 0) (implRunNondetOne 0) := hEnv 0
    have hEq : (0 : Nat) = 1 := by
      simp [EqSafe, natUnitModel, refRunDetZero, implRunNondetOne] at h0
    exact Nat.zero_ne_one hEq

/-- Interpreter with duplicate-sensitive delta (increment). -/
def interpReplayUnsafe : OpCoreInterpreter Nat Unit Unit Unit where
  causalGuard := fun _ _ _ => true
  delta := fun _ _ s => s + 1

/-- Reference run where an operation is delivered once. -/
def refRunSingleDelivery : Run Nat :=
  fun n => if n = 0 then evalCore interpReplayUnsafe unitOpCore () 0 else 0

/-- Implementation run where the same operation is replayed/duplicated at tick 0. -/
def implRunDuplicateDelivery : Run Nat :=
  fun n =>
    if n = 0 then
      evalCore interpReplayUnsafe unitOpCore ()
        (evalCore interpReplayUnsafe unitOpCore () 0)
    else
      0

/-- Without replay/duplication discipline, replay stability can fail. -/
theorem replayStable_fails_without_replayDiscipline :
    ¬ ReplayStableCoreEval interpReplayUnsafe := by
  intro hReplay
  have hAt0 := hReplay unitOpCore () 0
  have hEq : (2 : Nat) = 1 := by
    simp [evalCore, interpReplayUnsafe, unitOpCore] at hAt0
  exact (by decide : (2 : Nat) ≠ 1) hEq

/-- Duplicate delivery under non-idempotent deltas violates the envelope. -/
theorem envelopeCounterexample_without_replayDiscipline :
    ¬ Envelope natUnitModel refRunSingleDelivery implRunDuplicateDelivery := by
  intro hEnv
  have h0 : EqSafe natUnitModel (refRunSingleDelivery 0) (implRunDuplicateDelivery 0) := hEnv 0
  have hEq : (1 : Nat) = 2 := by
    simp [EqSafe, natUnitModel, refRunSingleDelivery, implRunDuplicateDelivery,
      evalCore, interpReplayUnsafe, unitOpCore] at h0
  exact (by decide : (1 : Nat) ≠ 2) hEq

/-- Combined OpCore boundary/minimality witness suite for removed components. -/
theorem opCore_boundary_minimality_counterexamples :
    (¬ Envelope natUnitModel refRunDenied implRunNoGuardDenied) ∧
      (evalCoreNondet 0 (implRunNondetOne 0) ∧
        ¬ Envelope natUnitModel refRunDetZero implRunNondetOne) ∧
      (¬ ReplayStableCoreEval interpReplayUnsafe ∧
        ¬ Envelope natUnitModel refRunSingleDelivery implRunDuplicateDelivery) := by
  refine ⟨envelopeCounterexample_without_causalGuard, ?_, ?_⟩
  · exact envelopeCounterexample_without_determinism
  · exact ⟨replayStable_fails_without_replayDiscipline,
      envelopeCounterexample_without_replayDiscipline⟩

end CRDT
end Distributed
