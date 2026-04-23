import Distributed.Families.TriangleOfForgetting.Core

set_option autoImplicit false

/-! # Distributed.Families.TriangleOfForgetting.GenericCausalState

Generic causal-state instantiations for the triangle-of-forgetting family.

This module supplies a reusable wrapper that can host any CRDT payload while
keeping the theorem-family interface from `Core` unchanged. The wrapper makes
causal history explicit, separates visible state from hidden compromise
metadata, and provides reusable bridges from concrete state-history facts to
the abstract triangle assumptions.
-/

/-
Turn the abstract triangle-of-forgetting predicates into something
that a concrete CRDT-style model can actually instantiate.

We want the wrapper to be reusable across different payloads and observer
projections. A useful model must talk about visible payload, horizons, membership,
and compromise metadata without hard-coding any particular CRDT semantics.

The file proceeds in four steps:
1. Define a generic causal state and a lightweight history vocabulary
2. Build triangle models from arbitrary payload observers and projections
3. Prove reusable ambiguity lemmas from visible-core and history hypotheses
4. Package those lemmas into a constructor for `TriangleOfForgetting.Assumptions`
-/

namespace Distributed
namespace TriangleOfForgetting
namespace GenericCausalState

universe uPayload uUpdate uMember uPayloadObs uView uOp uCtx uProg

/-! ## State, History, and Projections -/

/-- General causal state carrying an arbitrary payload, visible horizon, active
membership, and compromise metadata. -/
structure State (Payload : Type uPayload) (Member : Type uMember) where
  payload : Payload
  horizon : Nat
  activeMembers : Member → Prop
  compromisedMembers : Member → Prop

/-- Generic event vocabulary for causal histories layered over a causal state. -/
inductive HistoryEvent (Update : Type uUpdate) (Member : Type uMember) where
  | apply (u : Update)
  | join (m : Member)
  | leave (m : Member)
  | compromise (m : Member)
  | recover (m : Member)

/-- External causal history attached to states without constraining the payload. -/
abbrev History (Payload : Type uPayload) (Update : Type uUpdate) (Member : Type uMember) :=
  State Payload Member → List (HistoryEvent Update Member)

/-- History predicate: a leave event is recorded in the later state. -/
def LeaveRecorded
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    (history : History Payload Update Member)
    (s : State Payload Member) (m : Member) : Prop :=
  HistoryEvent.leave m ∈ history s

/-- History predicate: an update application is recorded in the current state. -/
def UpdateRecorded
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    (history : History Payload Update Member)
    (s : State Payload Member) (u : Update) : Prop :=
  HistoryEvent.apply u ∈ history s

/-- Observer-view projection over the visible part of a causal state. -/
abbrev Projection
    (Member : Type uMember)
    (PayloadObs : Type uPayloadObs)
    (View : Type uView) :=
  Member → PayloadObs → Nat → (Member → Prop) → View

/-- Admission policy for updates over a generic causal state. -/
abbrev AdmissionPolicy
    (Payload : Type uPayload)
    (Update : Type uUpdate)
    (Member : Type uMember) :=
  State Payload Member → Update → Prop

/-- Concrete observer view induced by a CRDT payload observer and a projection. -/
def observerView
    {Payload : Type uPayload} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (s : State Payload Member) (observer : Member) : View :=
  project observer (observePayload s.payload) s.horizon s.activeMembers

/-- Equality of the visible part of two causal states. -/
def SameVisibleCore
    {Payload : Type uPayload} {Member : Type uMember} {PayloadObs : Type uPayloadObs}
    (observePayload : Payload → PayloadObs)
    (s₁ s₂ : State Payload Member) : Prop :=
  observePayload s₁.payload = observePayload s₂.payload ∧
  s₁.horizon = s₂.horizon ∧
  s₁.activeMembers = s₂.activeMembers

/-- Default admission policy: accept exactly the updates that are currently live
according to the semantic horizon and active-membership boundary. -/
def semanticAccepts
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    (updateEpoch : Update → Nat)
    (author : Update → Member) :
    AdmissionPolicy Payload Update Member :=
  fun s u => updateEpoch u ≤ s.horizon ∧ s.activeMembers (author u)

/-! ## Triangle-Model Builders -/

/-- Minimal asynchronous reachability law used by the generic causal-state adapter:
every state can stutter while messages are delayed. -/
def AsynchronousReachability
    {Payload : Type uPayload} {Member : Type uMember}
    (reachable : State Payload Member → State Payload Member → Prop) : Prop :=
  ∀ s, reachable s s

/-- Build a triangle-of-forgetting model over a generic causal state. -/
def mkModel
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author) :
    Model (State Payload Member) Update Member View where
  reachable := reachable
  observerView := observerView observePayload project
  updateEpoch := updateEpoch
  author := author
  horizon := State.horizon
  memberActive := State.activeMembers
  compromised := State.compromisedMembers
  accepts := accepts
  asynchronous := AsynchronousReachability reachable

/-- Specialization of `mkModel` that uses any CRDT model's `observe` map as the
payload observer. -/
def modelOfCRDT
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    {Op : Type uOp} {Context : Type uCtx} {Program : Type uProg}
    (crdt : Distributed.CRDT.Model Payload Op Context PayloadObs Program)
    (reachable : State Payload Member → State Payload Member → Prop)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author) :
    Model (State Payload Member) Update Member View :=
  mkModel reachable crdt.observe project updateEpoch author accepts

/-! ## Visible-Core and History Hypotheses -/

/-- Recovery preserves the visible fields if it leaves payload observation,
horizon, and active membership unchanged. -/
def RecoveryPreservesVisibleCore
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author) :
    Prop :=
  let M := mkModel reachable observePayload project updateEpoch author accepts
  ∀ {m sComp sHeal},
    MemberRecovered M m sComp sHeal →
    SameVisibleCore observePayload sComp sHeal

/-- A recorded leave must come with some authored update that was already visible
before the leave. This is the causal-history bridge from membership removal to
revocation of something concrete. -/
def LeaveHistoryExplainsUpdate
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (history : History Payload Update Member) : Prop :=
  let M := mkModel reachable observePayload project updateEpoch author
  ∀ {sLive sExpired m},
    MemberLeft M m sLive sExpired →
    LeaveRecorded history sExpired m →
    ∃ u, UpdateRecorded history sLive u ∧ author u = m ∧ updateEpoch u ≤ sLive.horizon

/-- History package showing that supported leaves are explicitly recorded and
explained by a prior authored update. -/
def HistoryWitnessesRevocation
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (history : History Payload Update Member) : Prop :=
  let M := mkModel reachable observePayload project updateEpoch author
  (∀ {sLive sExpired m},
    MemberLeft M m sLive sExpired →
    LeaveRecorded history sExpired m) ∧
  LeaveHistoryExplainsUpdate reachable observePayload project updateEpoch author history

/-- A leave preserves some observer's projected view if every revocation witness
still admits a locally indistinguishable observer-state pair. This is weaker
than preserving the entire visible core, which would be too strong once
membership can actually change. -/
def LeavePreservesSomeObserverView
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author) :
    Prop :=
  let M := mkModel reachable observePayload project updateEpoch author accepts
  ∀ {sLive sExpired u},
    MemberLeft M (author u) sLive sExpired →
    LiveUpdate M sLive u →
    ∃ observer, IndistinguishableAt M observer sLive sExpired

/-! ## Generic Ambiguity Lemmas -/

/-- Equal visible cores imply indistinguishability for the projected view. -/
theorem indistinguishable_of_same_visible_core
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author)
    {observer : Member} {s₁ s₂ : State Payload Member}
    (hSame : SameVisibleCore observePayload s₁ s₂) :
    IndistinguishableAt
      (mkModel reachable observePayload project updateEpoch author accepts)
      observer s₁ s₂ := by
  -- Unpack visible-core equality and simplify the projected observer view.
  rcases hSame with ⟨hPayload, hHorizon, hActive⟩
  simp [IndistinguishableAt, mkModel, observerView, hPayload, hHorizon, hActive]

/-- Concrete recovery-ambiguity theorem for the generic causal-state model.
Any CRDT can be plugged in by choosing the payload type and observation map. -/
theorem compromise_recovery_ambiguity_of_recovery_witness
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author)
    (hPreserve :
      RecoveryPreservesVisibleCore reachable observePayload project updateEpoch author accepts)
    (hRecovery :
      RecoveryWitness (mkModel reachable observePayload project updateEpoch author accepts)) :
    CompromiseRecoveryAmbiguity (mkModel reachable observePayload project updateEpoch author accepts) := by
  -- A recovery witness becomes an ambiguity once recovery preserves the visible core.
  rcases hRecovery with ⟨sComp, sHeal, u, hRecovered, hCompromised⟩
  refine ⟨author u, sComp, sHeal, u, ?_, hRecovered, hCompromised⟩
  exact indistinguishable_of_same_visible_core
    reachable observePayload project updateEpoch author accepts (hPreserve hRecovered)

/-- CRDT-specialized recovery-ambiguity theorem reusing a CRDT's `observe` map. -/
theorem compromise_recovery_ambiguity_of_crdt_recovery_witness
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    {Op : Type uOp} {Context : Type uCtx} {Program : Type uProg}
    (crdt : Distributed.CRDT.Model Payload Op Context PayloadObs Program)
    (reachable : State Payload Member → State Payload Member → Prop)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author)
    (hPreserve :
      RecoveryPreservesVisibleCore reachable crdt.observe project updateEpoch author accepts)
    (hRecovery :
      RecoveryWitness (modelOfCRDT crdt reachable project updateEpoch author accepts)) :
    CompromiseRecoveryAmbiguity (modelOfCRDT crdt reachable project updateEpoch author accepts) := by
  -- The CRDT instance is just the generic theorem specialized to `crdt.observe`.
  simpa [modelOfCRDT] using
    compromise_recovery_ambiguity_of_recovery_witness
      reachable crdt.observe project updateEpoch author accepts hPreserve hRecovery

/-- Supported leaves plus a causal history witness yield a concrete
revocation witness. -/
theorem revocation_witness_of_history
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (history : History Payload Update Member)
    (hHistory : HistoryWitnessesRevocation reachable observePayload project updateEpoch author history)
    (hLeaves : SupportsLeaves (mkModel reachable observePayload project updateEpoch author)) :
    RevocationWitness (mkModel reachable observePayload project updateEpoch author) := by
  -- Pick a supported leave, then use the history witness to recover a concrete update.
  rcases hLeaves with ⟨sLive, sExpired, m, hLeft⟩
  have hRecorded : LeaveRecorded history sExpired m := hHistory.1 hLeft
  rcases hHistory.2 hLeft hRecorded with ⟨u, _hUpdateRecorded, hAuthor, hEpoch⟩
  refine ⟨sLive, sExpired, u, ?_, ?_⟩
  · -- Repackage the leave witness for the concrete authored update.
    rcases hLeft with ⟨hReach, hActive, hInactive⟩
    refine ⟨hReach, ?_, ?_⟩
    · simpa [mkModel, hAuthor] using hActive
    · simpa [mkModel, hAuthor] using hInactive
  · -- The history witness also provides the pre-leave liveness bound.
    refine ⟨hEpoch, ?_⟩
    simpa [mkModel, hAuthor] using hLeft.2.1

/-- CRDT-specialized revocation-witness theorem using an external causal history. -/
theorem revocation_witness_of_crdt_history
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    {Op : Type uOp} {Context : Type uCtx} {Program : Type uProg}
    (crdt : Distributed.CRDT.Model Payload Op Context PayloadObs Program)
    (reachable : State Payload Member → State Payload Member → Prop)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (history : History Payload Update Member)
    (hHistory : HistoryWitnessesRevocation reachable crdt.observe project updateEpoch author history)
    (hLeaves : SupportsLeaves (modelOfCRDT crdt reachable project updateEpoch author)) :
    RevocationWitness (modelOfCRDT crdt reachable project updateEpoch author) := by
  -- The CRDT specialization reuses the generic history-to-revocation bridge.
  simpa [modelOfCRDT] using
    revocation_witness_of_history
      reachable crdt.observe project updateEpoch author history hHistory hLeaves

/-- Concrete revocation-ambiguity theorem for the generic causal-state model.
Any CRDT can be plugged in by choosing the payload type and observation map. -/
theorem late_vs_invalid_ambiguity_of_revocation_witness
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author)
    (hPreserve :
      LeavePreservesSomeObserverView reachable observePayload project updateEpoch author accepts)
    (hRevocation :
      RevocationWitness (mkModel reachable observePayload project updateEpoch author accepts)) :
    LateVsInvalidAmbiguity (mkModel reachable observePayload project updateEpoch author accepts) := by
  -- A revocation witness becomes a late/invalid ambiguity once some observer's
  -- projected view is preserved across the leave.
  rcases hRevocation with ⟨sLive, sExpired, u, hLeft, hLive⟩
  rcases hPreserve hLeft hLive with ⟨observer, hIndist⟩
  refine ⟨observer, sLive, sExpired, u, hIndist, hLeft, hLive, ?_⟩
  exact expired_of_member_left_author hLeft

/-- CRDT-specialized revocation-ambiguity theorem reusing a CRDT's `observe` map. -/
theorem late_vs_invalid_ambiguity_of_crdt_revocation_witness
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    {Op : Type uOp} {Context : Type uCtx} {Program : Type uProg}
    (crdt : Distributed.CRDT.Model Payload Op Context PayloadObs Program)
    (reachable : State Payload Member → State Payload Member → Prop)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author)
    (hPreserve :
      LeavePreservesSomeObserverView reachable crdt.observe project updateEpoch author accepts)
    (hRevocation :
      RevocationWitness (modelOfCRDT crdt reachable project updateEpoch author accepts)) :
    LateVsInvalidAmbiguity (modelOfCRDT crdt reachable project updateEpoch author accepts) := by
  -- The CRDT instance is again just the generic theorem specialized to `crdt.observe`.
  simpa [modelOfCRDT] using
    late_vs_invalid_ambiguity_of_revocation_witness
      reachable crdt.observe project updateEpoch author accepts hPreserve hRevocation

/-! ## Assumption Packaging -/

/-- Helper constructor packaging the triangle assumptions from generic causal-state
lemmas. This keeps the theorem family reusable while letting concrete CRDT-style
models discharge the ambiguity assumptions constructively. -/
def assumptionsOfGenericModel
    {Payload : Type uPayload} {Update : Type uUpdate} {Member : Type uMember}
    {PayloadObs : Type uPayloadObs} {View : Type uView}
    (reachable : State Payload Member → State Payload Member → Prop)
    (observePayload : Payload → PayloadObs)
    (project : Projection Member PayloadObs View)
    (updateEpoch : Update → Nat)
    (author : Update → Member)
    (accepts : AdmissionPolicy Payload Update Member := semanticAccepts updateEpoch author)
    (history : History Payload Update Member)
    (hAsync : AsynchronousReachability reachable)
    (hLocalAcceptance :
      let M := mkModel reachable observePayload project updateEpoch author accepts
      ∀ ⦃observer s₁ s₂ u⦄,
        IndistinguishableAt M observer s₁ s₂ →
        (M.accepts s₁ u ↔ M.accepts s₂ u))
    (hHistory :
      HistoryWitnessesRevocation reachable observePayload project updateEpoch author history)
    (hLeavePreserve :
      LeavePreservesSomeObserverView reachable observePayload project updateEpoch author accepts)
    (hRecoverPreserve :
      RecoveryPreservesVisibleCore reachable observePayload project updateEpoch author accepts) :
    Assumptions (mkModel reachable observePayload project updateEpoch author accepts) :=
  { asynchronous := by
      -- The generic builder treats stutter/delay reachability as explicit evidence.
      exact hAsync
  , localAcceptance := hLocalAcceptance
  , dynamicMembershipProvidesRevocation := by
      -- The history bridge turns the leave half of dynamic membership into a revocation witness.
      intro hDyn
      exact revocation_witness_of_history
        reachable observePayload project updateEpoch author history hHistory hDyn.2
  , revocationCreatesAmbiguity := by
      -- Leave-side observer preservation transports revocation into ambiguity.
      intro hRev
      exact late_vs_invalid_ambiguity_of_revocation_witness
        reachable observePayload project updateEpoch author accepts hLeavePreserve hRev
  , recoveryWitnessCreatesAmbiguity := by
      -- Recovery-side visible-core preservation transports recovery into ambiguity.
      intro hRec
      exact compromise_recovery_ambiguity_of_recovery_witness
        reachable observePayload project updateEpoch author accepts hRecoverPreserve hRec
  }

end GenericCausalState
end TriangleOfForgetting
end Distributed
