import Distributed.Families.CRDT.Core.CoreModel
set_option autoImplicit false

/-! # Distributed.Families.TriangleOfForgetting.Core

## Expose

The semantic interface is:
- `Model`, `IndistinguishableAt`, `MemberLeft`, `MemberJoined`, `MemberRecovered`
- `LiveUpdate`, `ExpiredUpdate`, `CompromisedLiveUpdate`, `RevocationWitness`, `RecoveryWitness`
- `MonotoneMerge`, `ForwardSecrecy`, `PostCompromiseSecurity`, `TemporalSecrecy`
- `SupportsJoins`, `SupportsLeaves`, `DynamicMembership`
- `LateVsInvalidAmbiguity`, `CompromiseRecoveryAmbiguity`, `Assumptions`, `TriangleGuarantee`

Informally, the triangle of forgetting says that an asynchronous replicated
system cannot simultaneously provide all three of the following once validity
depends on information that may be hidden by delay:

1. `MonotoneMerge`: a still-live update remains mergeable when it arrives late
2. `TemporalSecrecy`: updates must eventually stop counting after revocation or
   post-compromise recovery
3. `DynamicMembership`: the member set supports both joins and leaves

The obstruction is local indistinguishability: the same visible update can be
merely late in one global state and security-invalid in another.
-/

/-
Package a reusable theorem family for the impossibility of
combining monotone merge, temporal secrecy, and dynamic membership in an
asynchronous setting once delayed and invalid updates can look the same to some
observer.

The difficulty is balancing reuse against precision: membership churn means
both joins and leaves, temporal secrecy means forward secrecy plus
post-compromise security, and ambiguity is observer-local indistinguishability.
Concrete causal-state and CRDT instantiations live in
`Distributed.Families.TriangleOfForgetting.GenericCausalState`.
-/

namespace Distributed
namespace TriangleOfForgetting
universe u v w x

/-! ## Model and Semantic Predicates -/

/-- Minimal model interface for triangle-of-forgetting reasoning. -/
structure Model
    (State : Type u)
    (Update : Type v)
    (Member : Type w)
    (View : Type x) where
  reachable : State → State → Prop
  observerView : State → Member → View
  updateEpoch : Update → Nat
  author : Update → Member
  horizon : State → Nat
  memberActive : State → Member → Prop
  compromised : State → Member → Prop
  accepts : State → Update → Prop
  asynchronous : Prop

/-- Two states are locally indistinguishable to one observer. -/
def IndistinguishableAt
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (observer : Member) (s₁ s₂ : State) : Prop :=
  M.observerView s₁ observer = M.observerView s₂ observer

/-- A member leaves between two reachable states. -/
def MemberLeft
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (m : Member) (s₁ s₂ : State) : Prop :=
  M.reachable s₁ s₂ ∧ M.memberActive s₁ m ∧ ¬ M.memberActive s₂ m

/-- A member joins between two reachable states. -/
def MemberJoined
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (m : Member) (s₁ s₂ : State) : Prop :=
  M.reachable s₁ s₂ ∧ ¬ M.memberActive s₁ m ∧ M.memberActive s₂ m

/-- A member's status changes between two reachable states, either by joining or leaving. -/
def MembershipChanged
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (m : Member) (s₁ s₂ : State) : Prop :=
  MemberLeft M m s₁ s₂ ∨ MemberJoined M m s₁ s₂

/-- A compromised member later recovers between two reachable states. -/
def MemberRecovered
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (m : Member) (s₁ s₂ : State) : Prop :=
  M.reachable s₁ s₂ ∧ M.compromised s₁ m ∧ ¬ M.compromised s₂ m

/-- An update is still live if it is within the state's horizon and its author remains active. -/
def LiveUpdate
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (s : State) (u : Update) : Prop :=
  M.updateEpoch u ≤ M.horizon s ∧ M.memberActive s (M.author u)

/-- An update is expired once it lies past the horizon or its author is no longer active. -/
def ExpiredUpdate
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (s : State) (u : Update) : Prop :=
  M.horizon s < M.updateEpoch u ∨ ¬ M.memberActive s (M.author u)

/-- A compromised-live update is still mergeable at the compromise point while its
author is currently compromised. -/
def CompromisedLiveUpdate
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View)
    (s : State) (u : Update) : Prop :=
  LiveUpdate M s u ∧ M.compromised s (M.author u)

/-- The late-vs-invalid ambiguity central to the impossibility result. -/
def LateVsInvalidAmbiguity
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∃ observer sLate sInvalid u,
    IndistinguishableAt M observer sLate sInvalid ∧
    MemberLeft M (M.author u) sLate sInvalid ∧
    LiveUpdate M sLate u ∧
    ExpiredUpdate M sInvalid u

/-- A compromise/recovery ambiguity: an update is locally seen as still mergeable
at compromise time but should be rejected after recovery. -/
def CompromiseRecoveryAmbiguity
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∃ observer sComp sHeal u,
    IndistinguishableAt M observer sComp sHeal ∧
    MemberRecovered M (M.author u) sComp sHeal ∧
    CompromisedLiveUpdate M sComp u

/-- Either a revocation ambiguity or a compromise/recovery ambiguity can force
the system to choose between merging and forgetting. -/
def TemporalSecurityAmbiguity
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  LateVsInvalidAmbiguity M ∨ CompromiseRecoveryAmbiguity M

/-- Monotone merge: every still-live update remains admissible for merge. -/
def MonotoneMerge
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∀ ⦃s u⦄, LiveUpdate M s u → M.accepts s u

/-- Forward secrecy: once an author leaves, any update live before that leave is rejected afterwards. -/
def ForwardSecrecy
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∀ ⦃sLive sExpired u⦄,
    MemberLeft M (M.author u) sLive sExpired →
    M.updateEpoch u ≤ M.horizon sLive →
    ¬ M.accepts sExpired u

/-- Post-compromise security: after recovery, updates already live at compromise time are rejected. -/
def PostCompromiseSecurity
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∀ ⦃sComp sHeal u⦄,
    MemberRecovered M (M.author u) sComp sHeal →
    CompromisedLiveUpdate M sComp u →
    ¬ M.accepts sHeal u

/-- Temporal secrecy is the combined demand of forward secrecy and post-compromise security. -/
def TemporalSecrecy
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ForwardSecrecy M ∧ PostCompromiseSecurity M

/-- The system supports membership joins. -/
def SupportsJoins
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∃ sJoinBefore sJoinAfter m, MemberJoined M m sJoinBefore sJoinAfter

/-- The system supports membership leaves. -/
def SupportsLeaves
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∃ sLeaveBefore sLeaveAfter m, MemberLeft M m sLeaveBefore sLeaveAfter

/-- Dynamic membership means the system supports both joins and leaves. -/
def DynamicMembership
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  SupportsJoins M ∧ SupportsLeaves M

/-- A revocation witness: some authored update is live before a leave and expired after it. -/
def RevocationWitness
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∃ sLive sExpired u,
    MemberLeft M (M.author u) sLive sExpired ∧
    LiveUpdate M sLive u

/-- A compromise/recovery witness: some update is live during compromise and the
author later recovers. -/
def RecoveryWitness
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  ∃ sComp sHeal u,
    MemberRecovered M (M.author u) sComp sHeal ∧
    CompromisedLiveUpdate M sComp u

/-- The combined guarantee ruled out by the triangle of forgetting. -/
def TriangleGuarantee
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop :=
  MonotoneMerge M ∧ TemporalSecrecy M ∧ DynamicMembership M

/-! ## Assumptions and Validation -/

/-- Proof-carrying validators report success because the assumption bundle stores the proof. -/
def proofCarryingValidationPassed : Bool :=
  decide (0 = 0)

/-- Reusable core triangle-of-forgetting assumption bundle. -/
structure Assumptions
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    (M : Model State Update Member View) : Prop where
  asynchronous : M.asynchronous
  localAcceptance :
    ∀ ⦃observer s₁ s₂ u⦄,
      IndistinguishableAt M observer s₁ s₂ →
      (M.accepts s₁ u ↔ M.accepts s₂ u)
  dynamicMembershipProvidesRevocation :
    DynamicMembership M → RevocationWitness M
  revocationCreatesAmbiguity :
    RevocationWitness M → LateVsInvalidAmbiguity M
  recoveryWitnessCreatesAmbiguity :
    RecoveryWitness M → CompromiseRecoveryAmbiguity M

/-- Built-in triangle-of-forgetting assumption labels for summary APIs. -/
inductive Assumption where
  | asynchronous
  | localAcceptance
  | dynamicMembershipProvidesRevocation
  | revocationCreatesAmbiguity
  | recoveryWitnessCreatesAmbiguity
  deriving Repr, DecidableEq, Inhabited

/-- Validation result for one triangle-of-forgetting assumption atom. -/
structure AssumptionResult where
  assumption : Assumption
  passed : Bool
  detail : String
  deriving Repr, DecidableEq, Inhabited

/-- Core reusable triangle-of-forgetting assumption set. -/
def coreAssumptions : List Assumption :=
  [ .asynchronous
  , .localAcceptance
  , .dynamicMembershipProvidesRevocation
  , .revocationCreatesAmbiguity
  , .recoveryWitnessCreatesAmbiguity
  ]

/-- Validate one assumption against an assumption bundle. -/
def validateAssumption
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (_a : Assumptions M) (h : Assumption) : AssumptionResult :=
  match h with
  | .asynchronous =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Asynchrony assumption is provided."
      }
  | .localAcceptance =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Local acceptance depends only on the observer-visible view."
      }
  | .dynamicMembershipProvidesRevocation =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Dynamic membership exposes a revocation witness."
      }
  | .revocationCreatesAmbiguity =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Revocation witnesses induce late-vs-invalid ambiguity."
      }
  | .recoveryWitnessCreatesAmbiguity =>
      { assumption := h
      , passed := proofCarryingValidationPassed
      , detail := "Recovery witnesses induce compromise/recovery ambiguity."
      }

/-- Validate a list of triangle-of-forgetting assumptions. -/
def validateAssumptions
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M) (hs : List Assumption) : List AssumptionResult :=
  hs.map (validateAssumption a)

/-- True iff every validation atom passed. -/
def allAssumptionsPassed (rs : List AssumptionResult) : Bool :=
  rs.all (fun r => r.passed)

/-- Summary of triangle-of-forgetting assumption validation. -/
structure AssumptionSummary where
  results : List AssumptionResult
  allPassed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Summary API for triangle-of-forgetting assumption validation. -/
def runAssumptionValidation
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M) (hs : List Assumption) :
    AssumptionSummary :=
  let rs := validateAssumptions a hs
  { results := rs, allPassed := allAssumptionsPassed rs }

/-! ## Derived Triangle-of-Forgetting Theorems -/

/-- A leave immediately yields expiration for the departed author's updates. -/
theorem expired_of_member_left_author
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    {sLive sExpired : State} {u : Update}
    (hLeft : MemberLeft M (M.author u) sLive sExpired) :
    ExpiredUpdate M sExpired u := by
  -- Expiration follows from the author's loss of active membership.
  exact Or.inr hLeft.2.2

/-- Forward secrecy rejects any update that was live before the author left. -/
theorem forward_secrecy_rejects_left_author
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (hFS : ForwardSecrecy M)
    {sLive sExpired : State} {u : Update}
    (hLeft : MemberLeft M (M.author u) sLive sExpired)
    (hLive : LiveUpdate M sLive u) :
    ¬ M.accepts sExpired u := by
  -- Forward secrecy consumes the leave witness and the pre-leave liveness bound.
  exact hFS hLeft hLive.1

/-- Post-compromise security rejects any update that was live during compromise
once the author has recovered. -/
theorem post_compromise_security_rejects_recovered_author
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (hPCS : PostCompromiseSecurity M)
    {sComp sHeal : State} {u : Update}
    (hRecovered : MemberRecovered M (M.author u) sComp sHeal)
    (hCompromised : CompromisedLiveUpdate M sComp u) :
    ¬ M.accepts sHeal u := by
  -- PCS applies directly to updates that were live at compromise time.
  exact hPCS hRecovered hCompromised

/-- Dynamic membership plus the revocation assumption yields a leave witness that
matters for some authored update. -/
theorem revocation_of_dynamic_membership
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hDyn : DynamicMembership M) :
    RevocationWitness M :=
  a.dynamicMembershipProvidesRevocation hDyn

/-- A revocation witness plus the ambiguity assumption yields the canonical
late/invalid pair. -/
theorem late_vs_invalid_of_revocation
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hRev : RevocationWitness M) :
    LateVsInvalidAmbiguity M :=
  a.revocationCreatesAmbiguity hRev

/-- A recovery witness plus the ambiguity assumption yields the canonical
compromise/recovery ambiguity pair. -/
theorem compromise_recovery_ambiguity_of_witness
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hRec : RecoveryWitness M) :
    CompromiseRecoveryAmbiguity M :=
  a.recoveryWitnessCreatesAmbiguity hRec

/-- Any temporal-security ambiguity conflicts with monotone merge plus temporal secrecy. -/
theorem impossibility_of_temporal_security_ambiguity
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hMerge : MonotoneMerge M)
    (hSecrecy : TemporalSecrecy M)
    (hAmbiguity : TemporalSecurityAmbiguity M) :
    False := by
  -- Split secrecy into the forward-secrecy and PCS obligations.
  rcases hSecrecy with ⟨hFS, hPCS⟩
  cases hAmbiguity with
  | inl hLate =>
      -- In the late/invalid branch, local indistinguishability transports acceptance.
      rcases hLate with
        ⟨observer, sLate, sInvalid, u, hIndist, hLeft, hLive, hExpired⟩
      have hAcceptLate : M.accepts sLate u := hMerge hLive
      have hAcceptInvalid : M.accepts sInvalid u :=
        (a.localAcceptance hIndist).1 hAcceptLate
      exact forward_secrecy_rejects_left_author hFS hLeft hLive hAcceptInvalid
  | inr hRecovery =>
      -- The recovery branch is the same transport argument, but uses PCS after healing.
      rcases hRecovery with
        ⟨observer, sComp, sHeal, u, hIndist, hRecovered, hCompromised⟩
      have hAcceptComp : M.accepts sComp u := hMerge hCompromised.1
      have hAcceptHeal : M.accepts sHeal u :=
        (a.localAcceptance hIndist).1 hAcceptComp
      exact post_compromise_security_rejects_recovered_author
        hPCS hRecovered hCompromised hAcceptHeal

/-- Full triangle-of-forgetting impossibility theorem in reusable-hypothesis form. -/
theorem impossibility_of_assumptions
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hTriangle : TriangleGuarantee M) :
    False := by
  -- Extract the three corners, then use dynamic membership to obtain a revocation witness.
  rcases hTriangle with ⟨hMerge, hSecrecy, hMembership⟩
  have hRevocation : RevocationWitness M :=
    revocation_of_dynamic_membership a hMembership
  have hAmbiguity : TemporalSecurityAmbiguity M :=
    Or.inl (late_vs_invalid_of_revocation a hRevocation)
  exact impossibility_of_temporal_security_ambiguity a hMerge hSecrecy hAmbiguity

/-- Corollary form: the triangle guarantee is impossible. -/
theorem not_triangle_guarantee_of_assumptions
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M) :
    ¬ TriangleGuarantee M := by
  -- Any witness to the full guarantee would contradict the main impossibility theorem.
  intro hTriangle
  exact impossibility_of_assumptions a hTriangle

/-- Monotone merge and dynamic membership force the failure of temporal secrecy. -/
theorem temporal_secrecy_impossible_of_monotone_merge_dynamic_membership
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hMerge : MonotoneMerge M)
    (hMembership : DynamicMembership M) :
    ¬ TemporalSecrecy M := by
  -- If secrecy held as well, the three corners would hold simultaneously.
  intro hSecrecy
  exact impossibility_of_assumptions a ⟨hMerge, hSecrecy, hMembership⟩

/-- Temporal secrecy and dynamic membership force the failure of monotone merge. -/
theorem monotone_merge_impossible_of_temporal_secrecy_dynamic_membership
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hSecrecy : TemporalSecrecy M)
    (hMembership : DynamicMembership M) :
    ¬ MonotoneMerge M := by
  -- Reordering the contradiction isolates monotone merge as the failing corner.
  intro hMerge
  exact impossibility_of_assumptions a ⟨hMerge, hSecrecy, hMembership⟩

/-- Monotone merge and temporal secrecy force the failure of dynamic membership. -/
theorem dynamic_membership_impossible_of_monotone_merge_temporal_secrecy
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hMerge : MonotoneMerge M)
    (hSecrecy : TemporalSecrecy M) :
    ¬ DynamicMembership M := by
  -- Reordering the contradiction isolates dynamic membership as the failing corner.
  intro hMembership
  exact impossibility_of_assumptions a ⟨hMerge, hSecrecy, hMembership⟩

/-- Monotone merge and temporal secrecy also conflict directly with
compromise/recovery ambiguity, using the PCS half of temporal secrecy. -/
theorem temporal_secrecy_impossible_of_monotone_merge_recovery_witness
    {State : Type u} {Update : Type v} {Member : Type w} {View : Type x}
    {M : Model State Update Member View}
    (a : Assumptions M)
    (hMerge : MonotoneMerge M)
    (hRecovery : RecoveryWitness M) :
    ¬ TemporalSecrecy M := by
  -- The recovery witness furnishes the ambiguity needed for the PCS branch directly.
  intro hSecrecy
  have hAmbiguity : TemporalSecurityAmbiguity M :=
    Or.inr (compromise_recovery_ambiguity_of_witness a hRecovery)
  exact impossibility_of_temporal_security_ambiguity a hMerge hSecrecy hAmbiguity

end TriangleOfForgetting
end Distributed
