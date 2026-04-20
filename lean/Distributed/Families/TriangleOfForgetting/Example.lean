import Distributed.Families.TriangleOfForgetting.API
import Distributed.Families.TriangleOfForgetting.GenericCausalState

set_option autoImplicit false

/-! # Distributed.Families.TriangleOfForgetting.Example

Worked example instantiating the generic triangle-of-forgetting causal-state
wrapper with a concrete CRDT payload.

The example uses `Distributed.CRDT.natUnitModel` as the payload observer and
builds explicit join, leave, compromise, and recovery states. It demonstrates
the reusable history and ambiguity lemmas, and it now packages them into a
fully certified triangle-of-forgetting impossibility protocol by supplying an
explicit local admission policy.
-/

/-
Show how to plug an ordinary CRDT into the generic causal-state
triangle machinery in a way that produces concrete revocation and recovery
witnesses.

The difficulty is balancing three goals at once:
- the model should stay small and explicit enough to read at a glance
- the observer projection should be coarse enough to witness ambiguity
- the local admission rule should depend only on the visible information carried
  by that projection

The file proceeds in four steps:
1. Define a tiny family of causal states, a coarse observer projection, and a
   visible admission rule
2. Prove the history and visibility hypotheses required by the generic lemmas
3. Materialize concrete join/leave support, revocation ambiguity, and recovery
   ambiguity for a CRDT-backed model
4. Package the resulting assumptions into a certified impossibility protocol
-/

namespace Distributed
namespace TriangleOfForgetting
namespace Example

open GenericCausalState

/-! ## Concrete Updates and States -/

abbrev Member := Nat
abbrev Payload := Nat
abbrev State := GenericCausalState.State Payload Member
abbrev View := Nat × Nat

/-- Minimal update record used by the example states. -/
structure Update where
  epoch : Nat
  author : Member
  deriving Repr, DecidableEq

/-- The leave-side update that is visible before revocation. -/
def uLeave : Update :=
  { epoch := 4, author := 0 }

/-- The recovery-side update that is visible during compromise. -/
def uRecover : Update :=
  { epoch := 6, author := 0 }

/-- Membership predicate with only member `0` active. -/
def active0 : Member → Prop :=
  fun m => m = 0

/-- Membership predicate with members `0` and `1` active. -/
def active01 : Member → Prop :=
  fun m => m = 0 ∨ m = 1

/-- Membership predicate with only member `1` active. -/
def active1 : Member → Prop :=
  fun m => m = 1

/-- Base state before a join occurs. -/
def sBase : State :=
  { payload := 1
  , horizon := 5
  , activeMembers := active0
  , compromisedMembers := fun _ => False
  }

/-- Join state where member `1` has been added. -/
def sJoin : State :=
  { payload := 2
  , horizon := 5
  , activeMembers := active01
  , compromisedMembers := fun _ => False
  }

/-- Leave state where member `0` has been removed. -/
def sLeave : State :=
  { payload := 2
  , horizon := 5
  , activeMembers := active1
  , compromisedMembers := fun _ => False
  }

/-- Compromise state where member `0` is still active but compromised. -/
def sComp : State :=
  { payload := 3
  , horizon := 7
  , activeMembers := active0
  , compromisedMembers := fun m => m = 0
  }

/-- Recovery state where compromise metadata has been cleared. -/
def sHeal : State :=
  { payload := 3
  , horizon := 7
  , activeMembers := active0
  , compromisedMembers := fun _ => False
  }

/-- Small explicit reachability relation for the worked example. -/
def reachable (s₁ s₂ : State) : Prop :=
  (s₁ = sBase ∧ s₂ = sJoin) ∨
  (s₁ = sJoin ∧ s₂ = sLeave) ∨
  (s₁ = sComp ∧ s₂ = sHeal)

/-- Coarse observer projection: observers see payload and horizon, but not
membership or compromise metadata. -/
def project : Projection Member Nat View :=
  fun _ payload horizon _ => (payload, horizon)

/-- Local admission policy used by the example: accept any update whose epoch is
within the visible horizon. This is intentionally coarser than semantic
validity, which is what makes the triangle contradiction possible. -/
def admitByHorizon : AdmissionPolicy Payload Update Member :=
  fun s u => u.epoch ≤ s.horizon

/-- Concrete CRDT-backed model used throughout the example. -/
def model : Model State Update Member View :=
  modelOfCRDT
    Distributed.CRDT.natUnitModel reachable project Update.epoch Update.author admitByHorizon

/-! ## Shape Lemmas -/

/-- The base and join states are distinct because their payloads differ. -/
theorem sBase_ne_sJoin : sBase ≠ sJoin := by
  intro hEq
  have hPayload := congrArg GenericCausalState.State.payload hEq
  simp [sBase, sJoin] at hPayload

/-- The leave and join states are distinct because their active-membership maps differ. -/
theorem sLeave_ne_sJoin : sLeave ≠ sJoin := by
  intro hEq
  have hActive := congrArg GenericCausalState.State.activeMembers hEq
  have hAtZero := congrFun hActive 0
  simp [sLeave, sJoin, active1, active01] at hAtZero

/-- The leave and base states are distinct because their payloads differ. -/
theorem sLeave_ne_sBase : sLeave ≠ sBase := by
  intro hEq
  have hPayload := congrArg GenericCausalState.State.payload hEq
  simp [sLeave, sBase] at hPayload

/-- Any leave witness in the example must be the `sJoin → sLeave` transition of member `0`. -/
theorem left_shape
    {m : Member} {sLive sExpired : State}
    (hLeft : MemberLeft model m sLive sExpired) :
    sLive = sJoin ∧ sExpired = sLeave ∧ m = 0 := by
  -- Split on the explicit reachability relation and rule out the non-leave branches.
  rcases hLeft with ⟨hReach, hActive, hInactive⟩
  rcases hReach with hBase | hTail
  · rcases hBase with ⟨rfl, rfl⟩
    exfalso
    have hZero : m = 0 := by
      simpa [model, modelOfCRDT, mkModel, sBase, active0] using hActive
    have hJoinActive : sJoin.activeMembers m := by
      simp [sJoin, active01, hZero]
    exact hInactive hJoinActive
  · rcases hTail with hLeave | hRecovery
    · rcases hLeave with ⟨rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      have hActive' : m = 0 ∨ m = 1 := by
        simpa [model, modelOfCRDT, mkModel, sJoin, active01] using hActive
      have hNotOne : ¬ m = 1 := by
        simpa [model, modelOfCRDT, mkModel, sLeave, active1] using hInactive
      cases hActive' with
      | inl hZero => exact hZero
      | inr hOne => exact False.elim (hNotOne hOne)
    · rcases hRecovery with ⟨rfl, rfl⟩
      exfalso
      exact hInactive hActive

/-- Any recovery witness in the example must be the `sComp → sHeal` transition of member `0`. -/
theorem recovered_shape
    {m : Member} {sCompromised sRecovered : State}
    (hRecovered : MemberRecovered model m sCompromised sRecovered) :
    sCompromised = sComp ∧ sRecovered = sHeal ∧ m = 0 := by
  -- Split on the explicit reachability relation and rule out the non-recovery branches.
  rcases hRecovered with ⟨hReach, hCompromised, hHealed⟩
  rcases hReach with hBase | hTail
  · rcases hBase with ⟨rfl, rfl⟩
    exfalso
    simp [model, modelOfCRDT, mkModel, sBase] at hCompromised
  · rcases hTail with hLeave | hRecovery
    · rcases hLeave with ⟨rfl, rfl⟩
      exfalso
      simp [model, modelOfCRDT, mkModel, sJoin] at hCompromised
    · rcases hRecovery with ⟨rfl, rfl⟩
      refine ⟨rfl, rfl, ?_⟩
      simpa [model, modelOfCRDT, mkModel, sComp] using hCompromised

/-! ## Concrete Membership Witnesses -/

/-- The example explicitly supports one membership join. -/
theorem supportsJoins : SupportsJoins model := by
  -- The `sBase → sJoin` transition adds member `1`.
  refine ⟨sBase, sJoin, 1, ?_⟩
  simp [MemberJoined, model, modelOfCRDT, mkModel, reachable,
    sBase, sJoin, active0, active01]

/-- The example explicitly supports one membership leave. -/
theorem supportsLeaves : SupportsLeaves model := by
  -- The `sJoin → sLeave` transition removes member `0`.
  refine ⟨sJoin, sLeave, 0, ?_⟩
  simp [MemberLeft, model, modelOfCRDT, mkModel, reachable,
    sJoin, sLeave, active01, active1]

/-- The example therefore has dynamic membership in the "joins and leaves" sense. -/
theorem dynamicMembership : DynamicMembership model := by
  -- Dynamic membership is the conjunction of the explicit join and leave witnesses.
  exact ⟨supportsJoins, supportsLeaves⟩

/-! ## Visibility Hypotheses -/

/-- Because the local admission rule reads only the visible horizon, any two
states with the same observer view induce the same admission decision. -/
theorem localAcceptance :
    ∀ ⦃observer s₁ s₂ u⦄,
      IndistinguishableAt model observer s₁ s₂ →
      (model.accepts s₁ u ↔ model.accepts s₂ u) := by
  intro observer s₁ s₂ u hIndist
  -- Equality of the projected `(payload, horizon)` view yields equal horizons.
  have hHorizon : s₁.horizon = s₂.horizon := by
    have hPair := hIndist
    simp [IndistinguishableAt, model, modelOfCRDT, mkModel, observerView, project] at hPair
    exact hPair.2
  -- The admission policy depends only on this visible horizon.
  simp [model, modelOfCRDT, mkModel, admitByHorizon, hHorizon]

/-- The coarse observer projection cannot distinguish the explicit leave pair,
because payload and horizon are unchanged across `sJoin → sLeave`. -/
theorem leavePreservesSomeObserverView :
    LeavePreservesSomeObserverView reachable Distributed.CRDT.natUnitModel.observe
      project Update.epoch Update.author admitByHorizon := by
  intro sLive sExpired u hLeft hLive
  -- The only leave pair is `sJoin → sLeave`, and the projection ignores membership.
  rcases left_shape hLeft with ⟨rfl, rfl, _hm⟩
  refine ⟨0, ?_⟩
  simp [IndistinguishableAt, mkModel, observerView,
    project, sJoin, sLeave]

/-- Recovery preserves the visible core because `sComp` and `sHeal` differ only
in hidden compromise metadata. -/
theorem recoveryPreservesVisibleCore :
    RecoveryPreservesVisibleCore reachable Distributed.CRDT.natUnitModel.observe
      project Update.epoch Update.author admitByHorizon := by
  intro m sCompromised sRecovered hRecovered
  -- The only recovery pair is `sComp → sHeal`, which keeps payload, horizon,
  -- and active membership fixed.
  rcases recovered_shape hRecovered with ⟨rfl, rfl, rfl⟩
  refine ⟨rfl, rfl, rfl⟩

/-! ## Materialized Revocation and Recovery Ambiguities -/

/-- The explicit leave pair and update form a concrete revocation witness. -/
theorem revocationWitness : RevocationWitness model := by
  -- Exhibit the concrete `sJoin → sLeave` leave together with the live update `uLeave`.
  refine ⟨sJoin, sLeave, uLeave, ?_, ?_⟩
  · simp [MemberLeft, model, modelOfCRDT, mkModel, reachable,
      sJoin, sLeave, uLeave, active01, active1]
  · simp [LiveUpdate, model, modelOfCRDT, mkModel, sJoin, uLeave, active01]

/-- The explicit leave pair yields the late-vs-invalid ambiguity promised by the generic wrapper. -/
theorem lateVsInvalidAmbiguity : LateVsInvalidAmbiguity model := by
  -- Combine the concrete revocation witness with the coarse observer projection.
  exact late_vs_invalid_ambiguity_of_crdt_revocation_witness
    Distributed.CRDT.natUnitModel reachable project Update.epoch Update.author admitByHorizon
    leavePreservesSomeObserverView revocationWitness

/-- The compromise state contains a live update authored by the compromised member. -/
theorem recoveryWitness : RecoveryWitness model := by
  -- Exhibit the concrete `sComp → sHeal` recovery transition together with `uRecover`.
  refine ⟨sComp, sHeal, uRecover, ?_, ?_⟩
  · refine ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ?_, ?_⟩
    · simp [model, modelOfCRDT, mkModel, sComp, uRecover]
    · simp [model, modelOfCRDT, mkModel, sHeal, uRecover]
  · refine ⟨?_, ?_⟩
    · refine ⟨by decide, ?_⟩
      change sComp.activeMembers uRecover.author
      simp [sComp, uRecover, active0]
    · change sComp.compromisedMembers uRecover.author
      simp [sComp, uRecover]

/-- The visible-core preservation theorem turns the recovery witness into a
concrete compromise/recovery ambiguity. -/
theorem compromiseRecoveryAmbiguity : CompromiseRecoveryAmbiguity model := by
  -- Use the generic CRDT recovery theorem with the explicit visible-core lemma.
  exact compromise_recovery_ambiguity_of_crdt_recovery_witness
    Distributed.CRDT.natUnitModel reachable project Update.epoch Update.author admitByHorizon
    recoveryPreservesVisibleCore recoveryWitness

/-! ## Certified Protocol Bundle -/

/-- The example packages its direct witnesses into the reusable triangle
assumption bundle. -/
def assumptions : Assumptions model :=
  { asynchronous := by trivial
  , localAcceptance := localAcceptance
  , dynamicMembershipProvidesRevocation := by
      intro _hDynamic
      exact revocationWitness
  , revocationCreatesAmbiguity := by
      intro _hWitness
      exact lateVsInvalidAmbiguity
  , recoveryWitnessCreatesAmbiguity := by
      intro _hWitness
      exact compromiseRecoveryAmbiguity
  }

/-- Certified impossibility bundle for the example model. -/
def protocol : ImpossibilityProtocol where
  State := State
  Update := Update
  Member := Member
  View := View
  model := model
  assumptions := assumptions

/-- The full triangle guarantee is impossible for the concrete example protocol. -/
theorem impossibility : ¬ TriangleGuarantee model :=
  impossibility_of_protocol protocol

/-- The packaged protocol validates every built-in triangle assumption. -/
theorem coreAssumptionsAllPassed :
    (runAssumptionValidation assumptions coreAssumptions).allPassed = true := by
  exact core_assumptions_all_passed protocol

end Example
end TriangleOfForgetting
end Distributed
