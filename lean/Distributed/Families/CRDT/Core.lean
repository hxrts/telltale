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

/-- Rich continuations erase to `OpCore` payloads. -/
abbrev ErasureMap (KRich : Type z) (OpTag : Type v) (Args : Type w) :=
  KRich → OpCore OpTag Args

/-- Erasure soundness: rich execution and erased-core execution agree observably. -/
def ErasureSoundness
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (evalRich : KRich → Context → State → State)
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ∀ kr ctx s, EqSafe M (evalRich kr ctx s) (evalCore interp (erase kr) ctx s)

/-- Erasure completeness: each `OpCore` behavior is realizable by some rich continuation. -/
def ErasureCompleteness
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ∀ kc : OpCore OpTag Args, ∃ kr : KRich,
    ∀ ctx s, EqSafe M (evalCore interp kc ctx s) (evalCore interp (erase kr) ctx s)

/-- Relative maximality: any equally-sound erasure factors through the chosen erasure. -/
def ErasureMaximality
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ∀ erase' : ErasureMap KRich OpTag Args,
    (∀ kr ctx s,
      EqSafe M (evalCore interp (erase' kr) ctx s) (evalCore interp (erase kr) ctx s)) →
      ∃ normalize : OpCore OpTag Args → OpCore OpTag Args,
        ∀ kr, erase' kr = normalize (erase kr)

/-- Weakest-core erasure theorem shape (soundness + completeness + maximality). -/
def WeakestOpCoreErasureTheorem
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (evalRich : KRich → Context → State → State)
    (interp : OpCoreInterpreter State Context OpTag Args)
    (erase : ErasureMap KRich OpTag Args) : Prop :=
  ErasureSoundness M evalRich interp erase ∧
  ErasureCompleteness M interp erase ∧
  ErasureMaximality M interp erase

/-- Lowering relation used by compile-time conformance gates. -/
abbrev LowerToCore (KRich : Type z) (OpTag : Type v) (Args : Type w) :=
  KRich → Option (OpCore OpTag Args)

/-- Compile-time gate: accept exactly when lowering evidence exists. -/
def conformanceGate
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (lower : LowerToCore KRich OpTag Args) (kr : KRich) : Bool :=
  (lower kr).isSome

/-- Conformance gate rejects operations that cannot be lowered to `OpCore`. -/
theorem conformanceGate_rejects_nonlowerable
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (lower : LowerToCore KRich OpTag Args) (kr : KRich)
    (h : lower kr = none) :
    conformanceGate lower kr = false := by
  simp [conformanceGate, h]

/-- Conformance gate accepts operations that lower to some `OpCore` payload. -/
theorem conformanceGate_accepts_lowerable
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (lower : LowerToCore KRich OpTag Args) (kr : KRich) (kc : OpCore OpTag Args)
    (h : lower kr = some kc) :
    conformanceGate lower kr = true := by
  simp [conformanceGate, h]

/-- Erasure premise bundle for least-expressive `OpCore` theorem proving. -/
structure ErasurePremises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (KRich : Type z) (OpTag : Type v) (Args : Type w) (Enc : Type x) :
    Type (max u v w x y z) where
  evalRich : KRich → Context → State → State
  interp : OpCoreInterpreter State Context OpTag Args
  erase : ErasureMap KRich OpTag Args
  lower : LowerToCore KRich OpTag Args
  encode : OpCore OpTag Args → Enc
  decode : Enc → Option (OpCore OpTag Args)
  weakestWitness : WeakestOpCoreErasureTheorem M evalRich interp erase
  replayStableWitness : ReplayStableCoreEval interp
  serializationWitness : TransportSerializationInvariant encode decode
  lowerSound : ∀ kr kc, lower kr = some kc → kc = erase kr

/-- Derive weakest-core erasure theorem from explicit erasure premises. -/
theorem weakestOpCoreErasure_of_premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) :
    WeakestOpCoreErasureTheorem M p.evalRich p.interp p.erase :=
  p.weakestWitness

/-- Derive replay stability of `OpCore` evaluation from erasure premises. -/
theorem opCoreReplayStable_of_premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) :
    ReplayStableCoreEval p.interp :=
  p.replayStableWitness

/-- Derive transport-serialization invariance from erasure premises. -/
theorem opCoreSerializationInvariant_of_premises
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) :
    TransportSerializationInvariant p.encode p.decode :=
  p.serializationWitness

/-- Conformance-gate theorem from lowering evidence. -/
theorem conformanceGate_of_loweringSound
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : ErasurePremises M KRich OpTag Args Enc) (kr : KRich) :
    conformanceGate p.lower kr = true ↔ ∃ kc, p.lower kr = some kc := by
  unfold conformanceGate
  constructor
  · intro hSome
    cases h : p.lower kr with
    | none =>
        simp [h] at hSome
    | some kc =>
        exact ⟨kc, rfl⟩
  · intro hLowered
    rcases hLowered with ⟨kc, hk⟩
    simp [hk]

/-- `ErasurePremises` viewed as an admissible serializable-AST continuation model. -/
abbrev SerializableASTContinuationModel
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (KRich : Type z) (OpTag : Type v) (Args : Type w) (Enc : Type x) :=
  ErasurePremises M KRich OpTag Args Enc

/-- Serializable continuation constructs unsupported by `OpCore` lowering. -/
def UnsupportedSerializableConstruct
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : SerializableASTContinuationModel M KRich OpTag Args Enc) (kr : KRich) : Prop :=
  p.lower kr = none

/-- Least-expressiveness: any admissible serializable AST model factors through `OpCore`. -/
theorem serializableAST_reducible_to_OpCore
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : SerializableASTContinuationModel M KRich OpTag Args Enc)
    (erase' : ErasureMap KRich OpTag Args)
    (hObs :
      ∀ kr ctx s,
        EqSafe M (evalCore p.interp (erase' kr) ctx s) (evalCore p.interp (p.erase kr) ctx s)) :
    ∃ normalize : OpCore OpTag Args → OpCore OpTag Args,
      ∀ kr, erase' kr = normalize (p.erase kr) := by
  exact (weakestOpCoreErasure_of_premises p).2.2 erase' hObs

/-- Classification theorem: rich constructs are either reducible to `OpCore` or rejected. -/
theorem serializableAST_reducible_or_rejected
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (p : SerializableASTContinuationModel M KRich OpTag Args Enc)
    (kr : KRich) (ctx : Context) (s : State) :
    (∃ kc, p.lower kr = some kc ∧ EqSafe M (p.evalRich kr ctx s) (evalCore p.interp kc ctx s)) ∨
      (UnsupportedSerializableConstruct p kr ∧ conformanceGate p.lower kr = false) := by
  cases hLower : p.lower kr with
  | none =>
      right
      exact ⟨hLower, conformanceGate_rejects_nonlowerable p.lower kr hLower⟩
  | some kc =>
      left
      have hSound : EqSafe M (p.evalRich kr ctx s) (evalCore p.interp (p.erase kr) ctx s) :=
        (weakestOpCoreErasure_of_premises p).1 kr ctx s
      have hk : kc = p.erase kr := p.lowerSound kr kc hLower
      refine ⟨kc, rfl, ?_⟩
      simpa [hk] using hSound

/-- A concrete rich continuation fragment equivalent to core payloads. -/
inductive CoreEquivalentKRich (OpTag : Type v) (Args : Type w) where
  | core : OpCore OpTag Args → CoreEquivalentKRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-- Erasure for the core-equivalent rich fragment. -/
def eraseCoreEquivalent
    {OpTag : Type v} {Args : Type w} :
    CoreEquivalentKRich OpTag Args → OpCore OpTag Args
  | .core kc => kc

/-- Rich evaluator for the core-equivalent fragment. -/
def evalRichCoreEquivalent
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    CoreEquivalentKRich OpTag Args → Context → State → State
  | .core kc, ctx, s => evalCore interp kc ctx s

/-- Lowering function for the core-equivalent fragment. -/
def lowerCoreEquivalent
    {OpTag : Type v} {Args : Type w} :
    LowerToCore (CoreEquivalentKRich OpTag Args) OpTag Args
  | .core kc => some kc

/-- Soundness for the core-equivalent erasure fragment. -/
theorem erasureSoundness_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ErasureSoundness M (evalRichCoreEquivalent interp) interp eraseCoreEquivalent := by
  intro kr ctx s
  cases kr with
  | core kc =>
      rfl

/-- Completeness for the core-equivalent erasure fragment. -/
theorem erasureCompleteness_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ErasureCompleteness M interp eraseCoreEquivalent := by
  intro kc
  refine ⟨CoreEquivalentKRich.core kc, ?_⟩
  intro ctx s
  rfl

/-- Maximality for the core-equivalent erasure fragment. -/
theorem erasureMaximality_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ErasureMaximality M interp eraseCoreEquivalent := by
  intro erase' _hEq
  refine ⟨fun kc => erase' (.core kc), ?_⟩
  intro kr
  cases kr with
  | core kc => rfl

/-- Weakest-core erasure theorem for the core-equivalent rich fragment. -/
theorem weakestOpCoreErasure_coreEquivalent
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    WeakestOpCoreErasureTheorem M (evalRichCoreEquivalent interp) interp eraseCoreEquivalent := by
  refine ⟨?_, ?_, ?_⟩
  · exact erasureSoundness_coreEquivalent M interp
  · exact erasureCompleteness_coreEquivalent M interp
  · exact erasureMaximality_coreEquivalent M interp

/-- Lowering soundness for the core-equivalent rich fragment. -/
theorem lowerCoreEquivalent_sound
    {OpTag : Type v} {Args : Type w}
    (kr : CoreEquivalentKRich OpTag Args) (kc : OpCore OpTag Args)
    (h : lowerCoreEquivalent kr = some kc) :
    kc = eraseCoreEquivalent kr := by
  cases kr with
  | core kc' =>
      simp [lowerCoreEquivalent] at h
      simpa [eraseCoreEquivalent] using h.symm

/-- Conformance gate accepts all core-equivalent rich continuations. -/
theorem conformanceGate_coreEquivalent_true
    {OpTag : Type v} {Args : Type w}
    (kr : CoreEquivalentKRich OpTag Args) :
    conformanceGate lowerCoreEquivalent kr = true := by
  cases kr with
  | core kc =>
      simp [conformanceGate, lowerCoreEquivalent]

/-- Families that are exactly representable by `OpCore` payloads. -/
class CoreRepresentableFamily
    (KRich : Type z) (OpTag : Type v) (Args : Type w) where
  toCore : KRich → OpCore OpTag Args
  ofCore : OpCore OpTag Args → KRich
  toCore_ofCore : ∀ kc, toCore (ofCore kc) = kc
  ofCore_toCore : ∀ kr, ofCore (toCore kr) = kr

/-- Rich-step evaluator induced by a core-representable family embedding. -/
def evalRichCoreRepresentable
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    {KRich : Type y} [CoreRepresentableFamily KRich OpTag Args] :
    KRich → Context → State → State
  | kr, ctx, s => evalCore interp (CoreRepresentableFamily.toCore kr) ctx s

/-- Total lowering induced by a core-representable family embedding. -/
def lowerCoreRepresentable
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    [CoreRepresentableFamily KRich OpTag Args] :
    LowerToCore KRich OpTag Args :=
  fun kr => some (CoreRepresentableFamily.toCore kr)

/-- Totality of lowering for core-representable rich families. -/
theorem lowerCoreRepresentable_total
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    [CoreRepresentableFamily KRich OpTag Args] :
    ∀ kr : KRich, ∃ kc,
      lowerCoreRepresentable (KRich := KRich) (OpTag := OpTag) (Args := Args) kr = some kc := by
  intro kr
  exact ⟨CoreRepresentableFamily.toCore kr, rfl⟩

/-- Pointwise observational preservation for core-representable lowering. -/
theorem stepObsPreserved_coreRepresentable
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    [CoreRepresentableFamily KRich OpTag Args]
    (interp : OpCoreInterpreter State Context OpTag Args) :
    ∀ kr ctx s kc,
      lowerCoreRepresentable (KRich := KRich) (OpTag := OpTag) (Args := Args) kr = some kc →
        EqSafe M (evalRichCoreRepresentable interp kr ctx s) (evalCore interp kc ctx s) := by
  intro kr ctx s kc hLower
  simp [lowerCoreRepresentable] at hLower
  subst kc
  rfl

/-- Adequacy witness for one rich-family lowering into `OpCore`. -/
structure FamilyLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (KRich : Type z) (OpTag : Type v) (Args : Type w) where
  interp : OpCoreInterpreter State Context OpTag Args
  evalRich : KRich → Context → State → State
  lower : LowerToCore KRich OpTag Args
  totalLowering : ∀ kr, ∃ kc, lower kr = some kc
  stepObsPreserved :
    ∀ kr ctx s kc, lower kr = some kc →
      EqSafe M (evalRich kr ctx s) (evalCore interp kc ctx s)

/-- Run-level envelope preservation induced by pointwise lowering adequacy. -/
theorem envelopePreserved_of_familyLowering
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (F : FamilyLoweringAdequacy M KRich OpTag Args)
    (runRich : Nat → KRich)
    (runCore : Nat → OpCore OpTag Args)
    (ctx : Context)
    (stateRun : Run State)
    (hLower : ∀ n, F.lower (runRich n) = some (runCore n)) :
    Envelope M
      (fun n => F.evalRich (runRich n) ctx (stateRun n))
      (fun n => evalCore F.interp (runCore n) ctx (stateRun n)) := by
  intro n
  exact F.stepObsPreserved (runRich n) ctx (stateRun n) (runCore n) (hLower n)

/-- Combined adequacy statement for one rich-family lowering. -/
def FamilyEnvelopeAdequate
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (F : FamilyLoweringAdequacy M KRich OpTag Args) : Prop :=
  (∀ kr, ∃ kc, F.lower kr = some kc) ∧
  (∀ kr ctx s kc, F.lower kr = some kc →
      EqSafe M (F.evalRich kr ctx s) (evalCore F.interp kc ctx s)) ∧
  (∀ (runRich : Nat → KRich) (runCore : Nat → OpCore OpTag Args)
      (ctx : Context) (stateRun : Run State),
      (∀ n, F.lower (runRich n) = some (runCore n)) →
        Envelope M
          (fun n => F.evalRich (runRich n) ctx (stateRun n))
          (fun n => evalCore F.interp (runCore n) ctx (stateRun n)))

/-- Every `FamilyLoweringAdequacy` witness yields `FamilyEnvelopeAdequate`. -/
theorem familyEnvelopeAdequate_of_lowering
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {KRich : Type z} {OpTag : Type v} {Args : Type w}
    (F : FamilyLoweringAdequacy M KRich OpTag Args) :
    FamilyEnvelopeAdequate M F := by
  refine ⟨F.totalLowering, F.stepObsPreserved, ?_⟩
  intro runRich runCore ctx stateRun hLower
  exact envelopePreserved_of_familyLowering F runRich runCore ctx stateRun hLower

/-- In-scope families bundled for adequacy obligations. -/
structure InScopeFamiliesAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    (RegisterRich CounterRich ORSetRich : Type z)
    (OpTag : Type v) (Args : Type w) where
  register : FamilyLoweringAdequacy M RegisterRich OpTag Args
  counter : FamilyLoweringAdequacy M CounterRich OpTag Args
  orset : FamilyLoweringAdequacy M ORSetRich OpTag Args

/-- Main adequacy theorem: every in-scope family lowers to `OpCore` with
observable and envelope preservation. -/
theorem inScopeFamilies_adequate
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {RegisterRich CounterRich ORSetRich : Type z}
    {OpTag : Type v} {Args : Type w}
    (A : InScopeFamiliesAdequacy M RegisterRich CounterRich ORSetRich OpTag Args) :
    FamilyEnvelopeAdequate M A.register ∧
    FamilyEnvelopeAdequate M A.counter ∧
    FamilyEnvelopeAdequate M A.orset := by
  refine ⟨familyEnvelopeAdequate_of_lowering A.register, ?_⟩
  exact ⟨familyEnvelopeAdequate_of_lowering A.counter,
    familyEnvelopeAdequate_of_lowering A.orset⟩

/-- Register CRDT rich fragment for in-scope lowering adequacy. -/
inductive RegisterRich (OpTag : Type v) (Args : Type w) where
  | op : OpCore OpTag Args → RegisterRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-- Counter CRDT rich fragment for in-scope lowering adequacy. -/
inductive CounterRich (OpTag : Type v) (Args : Type w) where
  | op : OpCore OpTag Args → CounterRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

/-- OR-Set CRDT rich fragment for in-scope lowering adequacy. -/
inductive ORSetRich (OpTag : Type v) (Args : Type w) where
  | op : OpCore OpTag Args → ORSetRich OpTag Args
  deriving Repr, DecidableEq, Inhabited

instance instCoreRepresentableFamilyRegisterRich
    {OpTag : Type v} {Args : Type w} :
    CoreRepresentableFamily (RegisterRich OpTag Args) OpTag Args where
  toCore
  | .op kc => kc
  ofCore kc := .op kc
  toCore_ofCore _ := rfl
  ofCore_toCore
  | .op _ => rfl

instance instCoreRepresentableFamilyCounterRich
    {OpTag : Type v} {Args : Type w} :
    CoreRepresentableFamily (CounterRich OpTag Args) OpTag Args where
  toCore
  | .op kc => kc
  ofCore kc := .op kc
  toCore_ofCore _ := rfl
  ofCore_toCore
  | .op _ => rfl

instance instCoreRepresentableFamilyORSetRich
    {OpTag : Type v} {Args : Type w} :
    CoreRepresentableFamily (ORSetRich OpTag Args) OpTag Args where
  toCore
  | .op kc => kc
  ofCore kc := .op kc
  toCore_ofCore _ := rfl
  ofCore_toCore
  | .op _ => rfl

/-- Lowering adequacy witness for in-scope register family. -/
def registerLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    FamilyLoweringAdequacy M (RegisterRich OpTag Args) OpTag Args :=
  { interp := interp
  , evalRich := evalRichCoreRepresentable interp
  , lower := lowerCoreRepresentable
  , totalLowering := lowerCoreRepresentable_total
  , stepObsPreserved := stepObsPreserved_coreRepresentable M interp
  }

/-- Lowering adequacy witness for in-scope counter family. -/
def counterLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    FamilyLoweringAdequacy M (CounterRich OpTag Args) OpTag Args :=
  { interp := interp
  , evalRich := evalRichCoreRepresentable interp
  , lower := lowerCoreRepresentable
  , totalLowering := lowerCoreRepresentable_total
  , stepObsPreserved := stepObsPreserved_coreRepresentable M interp
  }

/-- Lowering adequacy witness for in-scope OR-Set family. -/
def orsetLoweringAdequacy
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (interp : OpCoreInterpreter State Context OpTag Args) :
    FamilyLoweringAdequacy M (ORSetRich OpTag Args) OpTag Args :=
  { interp := interp
  , evalRich := evalRichCoreRepresentable interp
  , lower := lowerCoreRepresentable
  , totalLowering := lowerCoreRepresentable_total
  , stepObsPreserved := stepObsPreserved_coreRepresentable M interp
  }

/-- Concrete in-scope adequacy bundle for register/counter/OR-set families. -/
def inScopeFamiliesAdequacyCoreRepresentable
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program)
    {OpTag : Type v} {Args : Type w}
    (registerInterp counterInterp orsetInterp :
      OpCoreInterpreter State Context OpTag Args) :
    InScopeFamiliesAdequacy M (RegisterRich OpTag Args) (CounterRich OpTag Args)
      (ORSetRich OpTag Args) OpTag Args :=
  { register := registerLoweringAdequacy M registerInterp
  , counter := counterLoweringAdequacy M counterInterp
  , orset := orsetLoweringAdequacy M orsetInterp
  }

/-- Concrete adequacy theorem for representative in-scope CRDT families. -/
theorem inScopeFamilies_adequate_coreRepresentable
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program}
    {OpTag : Type v} {Args : Type w}
    (registerInterp counterInterp orsetInterp :
      OpCoreInterpreter State Context OpTag Args) :
    let A := inScopeFamiliesAdequacyCoreRepresentable M registerInterp counterInterp orsetInterp
    FamilyEnvelopeAdequate M A.register ∧
      FamilyEnvelopeAdequate M A.counter ∧
      FamilyEnvelopeAdequate M A.orset := by
  intro A
  exact inScopeFamilies_adequate A

/-- Hypothesis block matching `H_crdt_core`. -/
def HcrdtCore
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.semilatticeCoreClass ∧ M.opContextLayerClass

/-- Semilattice-only foundation predicate in the `H_crdt_core` analysis. -/
def SemilatticeOnlyFoundation
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.semilatticeCoreClass

/-- Distinct primitive algebra required for op-context CRDT correctness. -/
def OpContextPrimitiveAlgebra
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.opContextLayerClass

/-- Adequacy theorem: `H_crdt_core` is exactly semilattice + op-context primitive algebra. -/
theorem hcrdtCore_iff_semilattice_plus_opContext
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program} :
    HcrdtCore M ↔
      (SemilatticeOnlyFoundation M ∧ OpContextPrimitiveAlgebra M) := by
  rfl

/-- Concrete model where semilattice and op-context layers are both present. -/
def semilatticeWithOpContextModel : Model Nat Unit Unit Nat Unit where
  observe := natUnitModel.observe
  distance := natUnitModel.distance
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

/-- Concrete model where semilattice core exists but op-context layer is absent. -/
def semilatticeOnlyNoOpContextModel : Model Nat Unit Unit Nat Unit where
  observe := natUnitModel.observe
  distance := natUnitModel.distance
  semilatticeCoreClass := True
  opContextLayerClass := False
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

/-- Refutation witness: semilattice-only foundations do not imply op-context algebra. -/
theorem semilatticeOnly_not_sufficient_for_opContext :
    SemilatticeOnlyFoundation semilatticeOnlyNoOpContextModel ∧
      ¬ OpContextPrimitiveAlgebra semilatticeOnlyNoOpContextModel := by
  simp [SemilatticeOnlyFoundation, OpContextPrimitiveAlgebra, semilatticeOnlyNoOpContextModel]

/-- Universal refutation of deriving op-context from semilattice-only assumptions. -/
theorem hcrdtCore_refute_semilatticeOnly_derivation :
    ¬ (∀ M : Model Nat Unit Unit Nat Unit,
      SemilatticeOnlyFoundation M → OpContextPrimitiveAlgebra M) := by
  intro hDerive
  have hSemi : SemilatticeOnlyFoundation semilatticeOnlyNoOpContextModel := by
    simp [SemilatticeOnlyFoundation, semilatticeOnlyNoOpContextModel]
  have hOp : OpContextPrimitiveAlgebra semilatticeOnlyNoOpContextModel :=
    hDerive semilatticeOnlyNoOpContextModel hSemi
  simp [OpContextPrimitiveAlgebra, semilatticeOnlyNoOpContextModel] at hOp

/-- Distinct op-context primitive algebra is sufficient together with semilattice core. -/
theorem hcrdtCore_of_semilattice_plus_opContext
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    {M : Model State Op Context Obs Program} :
    SemilatticeOnlyFoundation M ∧ OpContextPrimitiveAlgebra M → HcrdtCore M := by
  intro h
  exact h

/-- Hypothesis block matching `H_crdt_foundation`. -/
def HcrdtFoundation
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.minimalOpStateEquivalenceAssumptions ∧ M.canonicalConvergenceDistanceClass

/-- Minimal assumption block for op/state equivalence analysis. -/
def MinimalOpStateConditions
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.minimalOpStateEquivalenceAssumptions

/-- Canonical convergence-distance assumption. -/
def CanonicalDConv
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.canonicalConvergenceDistanceClass

/-- Two concrete models witnessing non-canonicity of convergence distance. -/
def foundationModelDistance01 : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := False
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

/-- Companion model with same observables and a different valid distance. -/
def foundationModelDistance02 : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 2
  semilatticeCoreClass := True
  opContextLayerClass := True
  minimalOpStateEquivalenceAssumptions := True
  canonicalConvergenceDistanceClass := False
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

/-- Formal non-canonicity witness for `d_conv` under minimal assumptions. -/
theorem dconv_noncanonicity_counterexample :
    MinimalOpStateConditions foundationModelDistance01 ∧
      MinimalOpStateConditions foundationModelDistance02 ∧
      (∀ s, foundationModelDistance01.observe s = foundationModelDistance02.observe s) ∧
      (∃ s₁ s₂, foundationModelDistance01.distance s₁ s₂ ≠ foundationModelDistance02.distance s₁ s₂) := by
  refine ⟨by simp [MinimalOpStateConditions, foundationModelDistance01], ?_⟩
  refine ⟨by simp [MinimalOpStateConditions, foundationModelDistance02], ?_⟩
  refine ⟨by intro s; rfl, ?_⟩
  refine ⟨0, 1, ?_⟩
  simp [foundationModelDistance01, foundationModelDistance02]

/-- Refutation: minimal op/state assumptions alone do not force canonical `d_conv`. -/
theorem hcrdtFoundation_refute_canonical_from_minimal :
    ¬ (∀ M : Model Nat Unit Unit Nat Unit, MinimalOpStateConditions M → CanonicalDConv M) := by
  intro hDerive
  have hMin : MinimalOpStateConditions foundationModelDistance01 := by
    simp [MinimalOpStateConditions, foundationModelDistance01]
  have hCanon : CanonicalDConv foundationModelDistance01 :=
    hDerive foundationModelDistance01 hMin
  simp [CanonicalDConv, foundationModelDistance01] at hCanon

/-- Hypothesis block matching `H_crdt_dynamics`. -/
def HcrdtDynamics
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) : Prop :=
  M.mixingTimeControlledClass ∧ M.hotspotSlowModesClass ∧ M.driftDecayClass

/-- Run-level formalization of a mixing-time claim (eventual constancy). -/
def MixingTimeControlledRun (r : Run Nat) : Prop :=
  ∃ τ, ∀ t, τ ≤ t → r t = r τ

/-- Run-level formalization of hotspot slow-mode boundedness. -/
def HotspotSlowModeBoundedRun (r : Run Nat) : Prop :=
  ∃ B, ∀ t, r t ≤ B

/-- Run-level formalization of drift decay (eventual non-increasing trend). -/
def DriftDecayRun (r : Run Nat) : Prop :=
  ∃ τ, ∀ t, τ ≤ t → r (t + 1) ≤ r t

/-- Counterexample trace used to refute unconditional dynamics bounds. -/
def unboundedCounterexampleRun : Run Nat :=
  fun t => t

/-- Counterexample: the unbounded run does not satisfy mixing-time stabilization. -/
theorem unboundedRun_not_mixingTimeControlled :
    ¬ MixingTimeControlledRun unboundedCounterexampleRun := by
  intro hMix
  rcases hMix with ⟨τ, hτ⟩
  have hEq : unboundedCounterexampleRun (τ + 1) = unboundedCounterexampleRun τ :=
    hτ (τ + 1) (Nat.le_add_right τ 1)
  have hContra : τ + 1 = τ := by
    simp [unboundedCounterexampleRun] at hEq
  exact Nat.succ_ne_self τ hContra

/-- Counterexample: the unbounded run violates hotspot boundedness. -/
theorem unboundedRun_not_hotspotBounded :
    ¬ HotspotSlowModeBoundedRun unboundedCounterexampleRun := by
  intro hBounded
  rcases hBounded with ⟨B, hB⟩
  have hLe : unboundedCounterexampleRun (B + 1) ≤ B := hB (B + 1)
  have hContra : B + 1 ≤ B := by
    simpa [unboundedCounterexampleRun] using hLe
  exact Nat.not_succ_le_self B hContra

/-- Counterexample: the unbounded run does not satisfy drift decay. -/
theorem unboundedRun_not_driftDecay :
    ¬ DriftDecayRun unboundedCounterexampleRun := by
  intro hDecay
  rcases hDecay with ⟨τ, hτ⟩
  have hLe : unboundedCounterexampleRun (τ + 1) ≤ unboundedCounterexampleRun τ :=
    hτ τ (Nat.le_refl τ)
  have hContra : τ + 1 ≤ τ := by
    simpa [unboundedCounterexampleRun] using hLe
  exact Nat.not_succ_le_self τ hContra

/-- Refutation bundle for `H_crdt_dynamics` without explicit dissemination/fairness assumptions. -/
theorem hcrdtDynamics_counterexample_traces :
    ¬ MixingTimeControlledRun unboundedCounterexampleRun ∧
      ¬ HotspotSlowModeBoundedRun unboundedCounterexampleRun ∧
      ¬ DriftDecayRun unboundedCounterexampleRun := by
  exact ⟨unboundedRun_not_mixingTimeControlled,
    unboundedRun_not_hotspotBounded, unboundedRun_not_driftDecay⟩

/-- Hypothesis block matching `H_crdt_extensions`. -/
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

/-- Reusable core CRDT assumption bundle. -/
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


