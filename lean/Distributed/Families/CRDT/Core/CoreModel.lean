import Distributed.Families.CRDT.Core.Semilattice

set_option autoImplicit false

/-! # Distributed.Families.CRDT

Reusable CRDT theorem-family infrastructure:
- exact envelope characterization,
- observational adequacy modulo envelope,
- principal capability/admission claims,
- op/state equivalence,
- GC safety and bounded-approximation claims,
- the CRDT model as a join-semilattice with delta updates (`Model`).
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

/-- CRDT model: a join-semilattice of replica states, and for each update the
state-delta it contributes. A replica applies update `o` by joining `effect o`
(delta-state CRDT semantics). `observe`/`distance` are the safety-visible
projection and a convergence distance used by envelope statements. -/
structure Model
    (State : Type u)
    (Op : Type v)
    (Context : Type w)
    (Obs : Type x)
    (Program : Type y) where
  observe : State → Obs
  distance : State → State → Nat
  lattice : StateBasedCRDT State
  effect : Op → State

/-- Apply one update at a replica: join its delta. -/
def Model.apply
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) (o : Op) (s : State) : State :=
  M.lattice.join s (M.effect o)

/-- Replica state after delivering a list of updates to `base`, in list order. -/
def Model.deliver
    {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
    (M : Model State Op Context Obs Program) (base : State) (ops : List Op) : State :=
  ops.foldl (fun s o => M.apply o s) base

/-! ## Update Laws and Strong Eventual Consistency -/

section UpdateLaws

variable {State : Type u} {Op : Type v} {Context : Type w} {Obs : Type x} {Program : Type y}
  (M : Model State Op Context Obs Program)

/-- Updates are inflationary: a replica never loses information. -/
theorem Model.apply_inflationary (o : Op) (s : State) : M.lattice.le s (M.apply o s) :=
  M.lattice.join_left s (M.effect o)

/-- Updates are monotone in the replica state. -/
theorem Model.apply_monotone (o : Op) {s t : State} (h : M.lattice.le s t) :
    M.lattice.le (M.apply o s) (M.apply o t) :=
  merge_monotone_of_state_based_crdt M.lattice h (M.lattice.le_refl _)

/-- Re-delivering an update is a no-op (idempotence). -/
theorem Model.apply_idem (o : Op) (s : State) : M.apply o (M.apply o s) = M.apply o s := by
  simp only [Model.apply, M.lattice.join_assoc, M.lattice.join_idem]

/-- Delivering updates is merging their deltas. -/
theorem Model.deliver_eq_mergeAll (ops : List Op) :
    ∀ base, M.deliver base ops = mergeAll M.lattice base (ops.map M.effect) := by
  induction ops with
  | nil => intro base; rfl
  | cons o os ih => intro base; exact ih (M.apply o base)

/-- Strong eventual consistency for the model: replicas from the same base that
delivered the same set of updates (any order, duplicates allowed) are equal. -/
theorem Model.sec (base : State) (ops₁ ops₂ : List Op)
    (hSame : ∀ o, o ∈ ops₁ ↔ o ∈ ops₂) : M.deliver base ops₁ = M.deliver base ops₂ := by
  rw [M.deliver_eq_mergeAll, M.deliver_eq_mergeAll]
  apply strong_eventual_convergence_of_state_based_crdt
  intro x
  simp only [List.mem_map, hSame]

end UpdateLaws

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

/-- Simple concrete CRDT model (grow-only max register) used for OpCore boundary
counterexamples. -/
def natUnitModel : Model Nat Unit Unit Nat Unit where
  observe := fun s => s
  distance := fun s₁ s₂ => if s₁ = s₂ then 0 else 1
  lattice := natMaxCRDT
  effect := fun _ => 1

end CRDT
end Distributed
