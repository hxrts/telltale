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
that can be attached to protocol machine theorem packs, instead of keeping CRDT claims as prose only.
Solution Structure. Define a minimal CRDT model interface and proposition families,
then expose assumption bundles, validation helpers, and protocol-level API wrappers.
-/

/-! ## Core Development -/

namespace Distributed
namespace CRDT

universe u v w x y z

/-! ## Model Interface and Core Relations -/

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

/-! ## Envelope Theorem Forms -/

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

/-! ## Exactness and Adequacy Forms -/

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

/-! ## Budget and Capability Forms -/

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

/-! ## Equivalence and Approximation Forms -/

/-! ## State-Based CRDT Semantics -/

/-- Reusable state-based CRDT algebra: a join-semilattice with bottom. -/
structure StateBasedCRDT (State : Type u) where
  le : State → State → Prop
  join : State → State → State
  bottom : State
  le_refl : ∀ s, le s s
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  join_comm : ∀ a b, join a b = join b a
  join_idem : ∀ a, join a a = a
  join_left : ∀ a b, le a (join a b)
  join_right : ∀ a b, le b (join a b)
  join_lub : ∀ {a b c}, le a c → le b c → le (join a b) c
  bottom_le : ∀ a, le bottom a

/-- Merge is inflationary in both inputs. -/
def MergeInflationary {State : Type u} (S : StateBasedCRDT State) : Prop :=
  ∀ a b, S.le a (S.join a b) ∧ S.le b (S.join a b)

/-- Merge is monotone in both inputs. -/
def MergeMonotone {State : Type u} (S : StateBasedCRDT State) : Prop :=
  ∀ {a b c d}, S.le a c → S.le b d → S.le (S.join a b) (S.join c d)

/-- Strong eventual convergence for two replicas after exchanging the same states. -/
def StrongEventualConvergence {State : Type u} (S : StateBasedCRDT State) : Prop :=
  ∀ a b, S.join a b = S.join b a

/-- Sequentially merge a finite delivered state/update frontier. -/
def mergeAll {State : Type u} (S : StateBasedCRDT State) (base : State)
    (updates : List State) : State :=
  updates.foldl S.join base

/-- Two replicas have received the same finite causal frontier from the same base. -/
def SameFiniteCausalDelivery {State : Type u} (S : StateBasedCRDT State)
    (base : State) (updates : List State) (left right : State) : Prop :=
  left = mergeAll S base updates ∧ right = mergeAll S base updates

/-- Same finite causal delivery yields convergence. -/
def FiniteCausalDeliveryConverges {State : Type u} (S : StateBasedCRDT State) : Prop :=
  ∀ base updates left right,
    SameFiniteCausalDelivery S base updates left right → left = right

/-- Join laws imply inflationary merge. -/
theorem merge_inflationary_of_state_based_crdt
    {State : Type u} (S : StateBasedCRDT State) :
    MergeInflationary S := by
  intro a b
  exact ⟨S.join_left a b, S.join_right a b⟩

/-- Join laws imply merge monotonicity in both inputs. -/
theorem merge_monotone_of_state_based_crdt
    {State : Type u} (S : StateBasedCRDT State) :
    MergeMonotone S := by
  intro a b c d hAC hBD
  apply S.join_lub
  · exact S.le_trans hAC (S.join_left c d)
  · exact S.le_trans hBD (S.join_right c d)

/-- Join commutativity gives the two-replica SEC shape after state exchange. -/
theorem strong_eventual_convergence_of_state_based_crdt
    {State : Type u} (S : StateBasedCRDT State) :
    StrongEventualConvergence S :=
  S.join_comm

/-- Replicas with the same finite delivered causal frontier converge. -/
theorem finite_causal_delivery_converges_of_state_based_crdt
    {State : Type u} (S : StateBasedCRDT State) :
    FiniteCausalDeliveryConverges S := by
  intro _base _updates _left _right hDelivered
  exact hDelivered.1.trans hDelivered.2.symm

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

/-! ## OpCore Continuation and Evaluation -/

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
theorem eval_core_deterministic
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
theorem replay_stable_of_delta_idempotent
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (hIdem : DeltaIdempotent interp) :
    ReplayStableCoreEval interp := by
  intro k ctx s
  unfold evalCore
  by_cases h : interp.causalGuard ctx k.opTag k.args
  · simpa [h] using hIdem k.opTag k.args s
  · simp [h]

/-! ## Serialization Invariance Forms -/

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
theorem transport_serialization_invariant_of_round_trip
    {OpTag : Type v} {Args : Type w} {Enc : Type x}
    (encode : OpCore OpTag Args → Enc)
    (decode : Enc → Option (OpCore OpTag Args))
    (hRoundTrip : SerializationRoundTrip encode decode) :
    TransportSerializationInvariant encode decode :=
  hRoundTrip

/-! ## Guardless Evaluation Helper -/

/-- Evaluator variant without causal-guard checking (used for boundary counterexamples). -/
def evalCoreNoGuard
    {State : Type u} {Context : Type v} {OpTag : Type w} {Args : Type x}
    (interp : OpCoreInterpreter State Context OpTag Args)
    (k : OpCore OpTag Args) (_ctx : Context) (s : State) : State :=
  interp.delta k.opTag k.args s

/-- Simple concrete CRDT model used for OpCore boundary counterexamples. -/
structure NatSemilatticeCoreLaw : Prop where
  comm : ∀ a b : Nat, Nat.max a b = Nat.max b a

@[simp] theorem natSemilatticeCoreLaw : NatSemilatticeCoreLaw := by
  exact ⟨fun a b => Nat.max_comm a b⟩

structure UnitOpContextLayerLaw : Prop where
  unitContext : ∀ c : Unit, c = ()

@[simp] theorem unitOpContextLayerLaw : UnitOpContextLayerLaw := by
  exact ⟨by intro c; cases c; rfl⟩

structure NatOpStateEquivalenceLaw : Prop where
  refl : ∀ s : Nat, s = s

@[simp] theorem natOpStateEquivalenceLaw : NatOpStateEquivalenceLaw := by
  exact ⟨fun _ => rfl⟩

structure NatConvergenceDistanceLaw : Prop where
  selfZero : ∀ s : Nat, (if s = s then 0 else 1) = 0

@[simp] theorem natConvergenceDistanceLaw : NatConvergenceDistanceLaw := by
  exact ⟨by intro s; simp⟩

structure NatMixingControlLaw : Prop where
  reflexiveBound : ∀ t : Nat, t ≤ t

@[simp] theorem natMixingControlLaw : NatMixingControlLaw := by
  exact ⟨fun t => Nat.le_refl t⟩

structure NatHotspotSlowModeLaw : Prop where
  oneStepBound : ∀ s : Nat, s ≤ s + 1

@[simp] theorem natHotspotSlowModeLaw : NatHotspotSlowModeLaw := by
  exact ⟨fun s => Nat.le_succ s⟩

structure NatDriftDecayLaw : Prop where
  selfSubZero : ∀ s : Nat, s - s = 0

@[simp] theorem natDriftDecayLaw : NatDriftDecayLaw := by
  exact ⟨by intro s; simp⟩

structure NatSequenceSubclassLaw : Prop where
  successorFresh : ∀ i : Nat, i < i + 1

@[simp] theorem natSequenceSubclassLaw : NatSequenceSubclassLaw := by
  exact ⟨fun i => Nat.lt_succ_self i⟩

structure NatEpochBarrierLaw : Prop where
  epochReflexive : ∀ e : Nat, e ≤ e

@[simp] theorem natEpochBarrierLaw : NatEpochBarrierLaw := by
  exact ⟨fun e => Nat.le_refl e⟩

structure NatBoundedMetadataApproxLaw : Prop where
  oneStepBudget : ∀ t : Nat, t ≤ t + 1

@[simp] theorem natBoundedMetadataApproxLaw : NatBoundedMetadataApproxLaw := by
  exact ⟨fun t => Nat.le_succ t⟩

structure NatMultiscaleObservableLaw : Prop where
  observableRefl : ∀ s : Nat, s = s

@[simp] theorem natMultiscaleObservableLaw : NatMultiscaleObservableLaw := by
  exact ⟨fun _ => rfl⟩

structure NatMetadataFrontierLaw : Prop where
  frontierReflexive : ∀ t : Nat, t ≤ t

@[simp] theorem natMetadataFrontierLaw : NatMetadataFrontierLaw := by
  exact ⟨fun t => Nat.le_refl t⟩

structure NatGCCausalDominanceLaw : Prop where
  dominanceRefl : ∀ s : Nat, s = s

@[simp] theorem natGCCausalDominanceLaw : NatGCCausalDominanceLaw := by
  exact ⟨fun _ => rfl⟩

structure NatStabilizationLowerBoundLaw : Prop where
  nonnegativeTail : ∀ churn : Nat, 0 ≤ churn

@[simp] theorem natStabilizationLowerBoundLaw : NatStabilizationLowerBoundLaw := by
  exact ⟨fun churn => Nat.zero_le churn⟩

/-- Simple concrete CRDT model used for OpCore boundary counterexamples. -/
def natUnitModel : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  semilatticeCoreClass := NatSemilatticeCoreLaw
  opContextLayerClass := UnitOpContextLayerLaw
  minimalOpStateEquivalenceAssumptions := NatOpStateEquivalenceLaw
  canonicalConvergenceDistanceClass := NatConvergenceDistanceLaw
  mixingTimeControlledClass := NatMixingControlLaw
  hotspotSlowModesClass := NatHotspotSlowModeLaw
  driftDecayClass := NatDriftDecayLaw
  sequenceSubclassClass := NatSequenceSubclassLaw
  epochBarrierClass := NatEpochBarrierLaw
  boundedMetadataApproxClass := NatBoundedMetadataApproxLaw
  multiscaleObservablesClass := NatMultiscaleObservableLaw
  metadataTradeoffFrontierClass := NatMetadataFrontierLaw
  gcCausalDominanceClass := NatGCCausalDominanceLaw
  stabilizationLowerBoundClass := NatStabilizationLowerBoundLaw

end CRDT
end Distributed
