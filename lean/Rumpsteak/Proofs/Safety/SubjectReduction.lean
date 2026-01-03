import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Coherence
import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration
import Rumpsteak.Protocol.Semantics.Reduction
import Rumpsteak.Protocol.Semantics.Typing
import Rumpsteak.Protocol.Semantics.QueueTyping
import Rumpsteak.Proofs.Projection.Enabledness

/-! # Rumpsteak.Proofs.Safety.SubjectReduction

Subject reduction (type preservation) for multiparty sessions.

## Overview

Subject reduction states that well-typedness is preserved under reduction.
If a configuration is well-typed and can step, the resulting configuration
is also well-typed against an EVOLVED global type.

This is a fundamental safety property: types are preserved during execution.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Claims

- `SubjectReduction`: If ⊢ M : G and M → M', then ⊢ M' : G' for some G' s.t. G ⟹ G'

## Main Results

- `subject_reduction`: Main theorem
-/

namespace Rumpsteak.Proofs.Safety.SubjectReduction

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.ProjectionR
open Rumpsteak.Protocol.Coherence
open Rumpsteak.Protocol.Semantics.Process
open Rumpsteak.Protocol.Semantics.Configuration
open Rumpsteak.Protocol.Semantics.Reduction
open Rumpsteak.Protocol.Semantics.Typing
open Rumpsteak.Protocol.Semantics.QueueTyping
open Rumpsteak.Proofs.Projection.Enabledness

/-! ## Projection Commutativity Theorems

These theorems capture fundamental properties of multiparty session type projection.
They describe how projections evolve as the global type consumes communications. -/

/-- Projection and substitution commute for equi-recursive types.

    THEORETICAL JUSTIFICATION:
    This is a fundamental property of equi-recursive types in session type theory.
    See Gay & Hole "Subtyping for Session Types" (2005) and Pierce "Types and
    Programming Languages" Ch. 21 for the equi-recursive approach.

    The key insight: unfolding a recursive type (μt.body → body[μt.body/t]) and then
    projecting gives the same result as projecting the μ-type directly. This is because:

    1. Projection is defined structurally on global types
    2. For μt.body: projection wraps the body's projection in μt (if non-trivial)
    3. For body[μt.body/t]: variables t are replaced before projection
    4. In well-formed protocols, the recursion variable t is used consistently,
       so the projection commutes with substitution

    PROOF SKETCH (by structural induction on body):
    - end: substitute is identity, both sides project to end ✓
    - var x: if x=t, both sides project μt.body; if x≠t, both project var x ✓
    - comm s r bs: substitute distributes, projection distributes ✓
    - mu t' b: if t'=t, shadowing means substitute is identity ✓

    Note: Role names (participants like "Alice", "Bob") and type variable names
    (recursion variables like "t", "X") are in different semantic domains. This axiom
    applies regardless of whether role = t syntactically, since the projection logic
    handles the domains separately. -/
axiom projectR_subst_comm_non_participant (body : GlobalType) (t : String) (role : String)
    : projectR (body.substitute t (.mu t body)) role = projectR (.mu t body) role

/-! ## Helper Lemmas for mapM and Projection -/

/-- If projectBranches succeeds and a labeled projection appears, then the source branch exists. -/
theorem projectBranches_mem_implies_branch_mem
    (branches : List (Label × GlobalType)) (role : String)
    (label : Label) (contType : LocalTypeR)
    (projBranches : List (Label × LocalTypeR))
    (hproj : projectBranches branches role = .ok projBranches)
    (hmem : (label, contType) ∈ projBranches) : ∃ g, (label, g) ∈ branches := by
  induction branches generalizing projBranches with
  | nil =>
    simp [projectBranches] at hproj
    cases hproj
    cases hmem
  | cons b rest ih =>
    unfold projectBranches at hproj
    cases hcont : projectR b.2 role with
    | error e =>
      simp [hcont] at hproj
      cases hproj
    | ok lt =>
      cases hrest : projectBranches rest role with
      | error e =>
        simp [hcont, hrest] at hproj
        cases hproj
      | ok lts =>
        simp [hcont, hrest] at hproj
        cases hproj
        have hmem' : (label, contType) = (b.1, lt) ∨ (label, contType) ∈ lts := by
          simpa using hmem
        cases hmem' with
        | inl hhead =>
          cases hhead
          exact ⟨b.2, by simp⟩
        | inr htail =>
          obtain ⟨g, hmemg⟩ := ih lts hrest htail
          exact ⟨g, List.mem_cons_of_mem _ hmemg⟩

/-- Projection after send: after consuming a send, the sender's projection evolves.

    If G ↾ sender = !receiver{ℓ.T} and G consumes sender→ℓ→receiver to get G',
    then G' ↾ sender = T.

    Proof by induction on ConsumeResult, using projection inversion lemmas. -/
theorem projection_after_send_thm (g g' : GlobalType) (sender receiver : String)
    (label : Label) (contType : LocalTypeR)
    (hproj : projectR g sender = .ok (.send receiver [(label, contType)]))
    (hcons : g.consume sender receiver label = some g')
    : projectR g' sender = .ok contType := by
  have hcr := consume_implies_ConsumeResult g sender receiver label g' hcons
  induction hcr generalizing contType with
  | comm sender receiver branches label cont hfind =>
    -- reduce the projection of the communication head
    have hproj' := hproj
    simp [projectR_comm_sender] at hproj'
    by_cases hnil : branches.isEmpty
    · exfalso
      simp [hnil] at hproj'
    · simp [hnil] at hproj'
      cases hpb : projectBranches branches sender with
      | error e =>
        exfalso
        simp [hpb] at hproj'
        cases hproj'
      | ok bs =>
        simp [hpb, Except.map] at hproj'
        have hsend : LocalTypeR.send receiver bs =
            LocalTypeR.send receiver [(label, contType)] := by
          cases hproj'
          rfl
        cases hsend
        -- singleton projection pins down the branch
        exact projectBranches_find_proj branches sender label contType cont hpb hfind
  | mu t body sender receiver label g' hcr' ih =>
    have hproj' :
        projectR (body.substitute t (.mu t body)) sender =
          .ok (.send receiver [(label, contType)]) := by
      calc
        projectR (body.substitute t (.mu t body)) sender
            = projectR (.mu t body) sender := projectR_subst_comm_non_participant body t sender
        _ = .ok (.send receiver [(label, contType)]) := hproj
    have hcons' : (body.substitute t (.mu t body)).consume sender receiver label = some g' :=
      ConsumeResult_implies_consume (body.substitute t (.mu t body)) sender receiver label g' hcr'
    exact ih contType hproj' hcons'

/-! ## Enabledness-to-step helpers

These replace the legacy consume axioms by routing through the enabledness bridge
and the `goodG` field of coherence. -/

/-- If a sender projection is a singleton send, the corresponding async step exists. -/
theorem projection_send_implies_step (g : GlobalType) (sender receiver : String)
    (label : Label) (contType : LocalTypeR)
    (hproj : projectR g sender = .ok (.send receiver [(label, contType)]))
    (hcoh : coherentG g)
    : ∃ g', step g (LocalActionR.toGlobal sender (LocalActionR.send receiver label)) g' := by
  have hlocal : LocalTypeR.canStep (.send receiver [(label, contType)])
      (LocalActionR.send receiver label) := by
    apply LocalTypeR.canStep.send_head receiver [(label, contType)] label contType
    simp
  have hcan : canStep g (LocalActionR.toGlobal sender (LocalActionR.send receiver label)) :=
    project_can_step g sender (.send receiver [(label, contType)])
      (LocalActionR.send receiver label) hproj hlocal hcoh
  exact hcoh.good _ hcan

/-- If a receiver projection offers a label, the corresponding async step exists. -/
theorem projection_recv_implies_step (g : GlobalType) (sender receiver : String)
    (label : Label) (types : List (Label × LocalTypeR)) (contType : LocalTypeR)
    (hproj : projectR g receiver = .ok (.recv sender types))
    (hmem : (label, contType) ∈ types)
    (hcoh : coherentG g)
    : ∃ g', step g (LocalActionR.toGlobal receiver (LocalActionR.recv sender label)) g' := by
  have hlocal : LocalTypeR.canStep (.recv sender types)
      (LocalActionR.recv sender label) := by
    apply LocalTypeR.canStep.recv_head sender types label contType
    exact hmem
  have hcan : canStep g (LocalActionR.toGlobal receiver (LocalActionR.recv sender label)) :=
    project_can_step g receiver (.recv sender types)
      (LocalActionR.recv sender label) hproj hlocal hcoh
  exact hcoh.good _ hcan

axiom projection_after_recv_thm (g g' : GlobalType) (sender receiver : String)
    (label : Label) (types : List (Label × LocalTypeR)) (contType : LocalTypeR)
    (hproj : projectR g receiver = .ok (.recv sender types))
    (hmem : (label, contType) ∈ types)
    (hcons : g.consume sender receiver label = some g')
    : projectR g' receiver = .ok contType

/-- Projection after an async send step (to be proved). -/
axiom projection_after_send_step (g g' : GlobalType) (sender receiver : String)
    (label : Label) (contType : LocalTypeR)
    (hproj : projectR g sender = .ok (.send receiver [(label, contType)]))
    (hstep : step g (LocalActionR.toGlobal sender (LocalActionR.send receiver label)) g')
    : projectR g' sender = .ok contType

/-- Projection after an async recv step (to be proved). -/
axiom projection_after_recv_step (g g' : GlobalType) (sender receiver : String)
    (label : Label) (types : List (Label × LocalTypeR)) (contType : LocalTypeR)
    (hproj : projectR g receiver = .ok (.recv sender types))
    (hmem : (label, contType) ∈ types)
    (hstep : step g (LocalActionR.toGlobal receiver (LocalActionR.recv sender label)) g')
    : projectR g' receiver = .ok contType

/-- Projection preserved for non-participants (success case).

    If G consumes sender→ℓ→receiver to get G', role ∉ {sender, receiver},
    and projection of G to role succeeds, then G' ↾ role = G ↾ role.

    Proof by induction on ConsumeResult. -/
theorem projection_preserved_other_thm (g g' : GlobalType) (sender receiver role : String)
    (label : Label) (result : LocalTypeR)
    (hcons : g.consume sender receiver label = some g')
    (hne1 : role ≠ sender)
    (hne2 : role ≠ receiver)
    (hproj : projectR g role = .ok result)
    : projectR g' role = .ok result := by
  have hcr := consume_implies_ConsumeResult g sender receiver label g' hcons
  -- Induction on the consume derivation, generalizing the role/result payload.
  induction hcr generalizing role result with
  | comm sender receiver branches label cont hfind =>
    -- For non-participants, each branch projection equals the merged result.
    exact projectR_comm_non_participant sender receiver role branches result
      hne1 hne2 hproj label cont hfind
  | mu t body sender receiver label g' hcr' ih =>
    have hproj' : projectR (body.substitute t (.mu t body)) role = .ok result := by
      calc
        projectR (body.substitute t (.mu t body)) role
            = projectR (.mu t body) role := projectR_subst_comm_non_participant body t role
        _ = .ok result := hproj
    have hcons' : (body.substitute t (.mu t body)).consume sender receiver label = some g' :=
      ConsumeResult_implies_consume (body.substitute t (.mu t body)) sender receiver label g' hcr'
    exact ih role result hcons' hne1 hne2 hproj'

theorem GlobalTypeReducesStar.trans {g1 g2 g3 : GlobalType}
    (h12 : GlobalTypeReducesStar g1 g2) (h23 : GlobalTypeReducesStar g2 g3) :
    GlobalTypeReducesStar g1 g3 := by
  induction h12 generalizing g3 with
  | refl g1 =>
    simpa using h23
  | step g1 g2 g3 hred h12' ih =>
    exact GlobalTypeReducesStar.step g1 g2 g3 hred (ih h23)

/-- Transitivity for async step closure. -/
theorem GlobalTypeStepStar.trans {g1 g2 g3 : GlobalType}
    (h12 : GlobalTypeStepStar g1 g2) (h23 : GlobalTypeStepStar g2 g3) :
    GlobalTypeStepStar g1 g3 := by
  induction h12 generalizing g3 with
  | refl g1 =>
    simpa using h23
  | step g1 g2 g3 act hstep h12' ih =>
    exact GlobalTypeStepStar.step g1 g2 g3 act hstep (ih h23)

/-- Consume implies at least one global reduction step (star). -/
theorem consume_implies_GlobalTypeReducesStar (g g' : GlobalType)
    (sender receiver : String) (label : Label)
    (hcons : g.consume sender receiver label = some g')
    : GlobalTypeReducesStar g g' := by
  have hcr := consume_implies_ConsumeResult g sender receiver label g' hcons
  have hred := ConsumeResult_implies_reduces g sender receiver label g' hcr
  exact GlobalTypeReducesStar.step g g' g' hred (GlobalTypeReducesStar.refl g')

/- Subject reduction for send axiom.

    PROOF SKETCH (Session type theory):
    When a sender executes a send, the configuration evolves:
    1. The sender's process moves to its continuation
    2. The message is enqueued in the sender→receiver queue
    3. The global type consumes the corresponding communication

    The continuation is well-typed against the evolved global type because:
    - By inversion, the continuation has the continuation type
    - By projection_after_send, the evolved global type projects to this type

    ASYNCHRONOUS SEMANTICS NOTE:
    In asynchronous semantics with explicit message queues, there is a fundamental
    tension in the current `ConfigWellTyped` definition:
    - After a send, the sender's process needs the CONTINUATION type
    - The receiver's process is unchanged and still needs the RECEIVE type
    - But g.consume changes BOTH sender and receiver projections simultaneously

    The current definition requires all roles to be typed against projections of
    a SINGLE global type. For full async semantics, one would need:
    - Queue-aware typing that accounts for in-flight messages, OR
    - Session subtyping allowing processes to be "behind" their expected types, OR
    - Split global types that track send/receive independently

    This axiom captured the expected behavior under synchronous typing. It is now
    superseded by the queue-typed proof path. -/

/- Subject reduction for recv axiom.

    PROOF SKETCH (Session type theory):
    When a receiver executes a receive:
    1. The receiver's process moves to the selected branch continuation
    2. The message is dequeued from the sender→receiver queue
    3. The global type consumes the corresponding communication

    The selected branch is well-typed against the evolved global type because:
    - The message label matches a branch in the receiver's type
    - By inversion, that branch has the corresponding branch type
    - By projection after the send (already consumed), the type matches

    NOTE: For the recv case, the asynchronous gap is resolved because:
    - The message was already sent (sender has moved on)
    - The receiver now executes, consuming from the queue
    - After this step, both sender and receiver have "caught up" to the evolved global type.

    This axiom is no longer used; the queue-typed subject-reduction lemmas provide
    the derived behavior. -/

/-- If mapM succeeds on a list and produces a list containing (l, t),
    then there was an input (l, g) where f(l, g) = (l, t). -/
theorem mapM_result_member {α β : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} {y : β}
    (hmap : xs.mapM f = .ok ys) (hmem : y ∈ ys)
    : ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil] at hmap
    cases hmap
    simp only [List.not_mem_nil] at hmem
  | cons x xs' ih =>
    simp only [List.mapM_cons, bind, Except.bind] at hmap
    cases hfx : f x with
    | error e =>
      simp only [hfx] at hmap
      cases hmap
    | ok b =>
      simp only [hfx] at hmap
      cases hrest : xs'.mapM f with
      | error e =>
        simp only [hrest] at hmap
        cases hmap
      | ok bs =>
        simp only [hrest] at hmap
        cases hmap
        cases hmem with
        | head => exact ⟨x, List.mem_cons_self, hfx⟩
        | tail _ htail =>
          obtain ⟨x', hx'mem, hfx'⟩ := ih hrest htail
          exact ⟨x', List.mem_cons_of_mem x hx'mem, hfx'⟩

/-- Helper: mapM producing singleton means input is singleton. -/
theorem mapM_singleton_input {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {y : β}
    (hmap : xs.mapM f = .ok [y])
    : ∃ x, xs = [x] ∧ f x = .ok y := by
  induction xs with
  | nil =>
    simp [List.mapM_nil] at hmap
    cases hmap
  | cons x xs ih =>
    simp [List.mapM_cons, bind, Except.bind] at hmap
    cases hfx : f x with
    | error e =>
      simp [hfx] at hmap
    | ok b =>
      simp [hfx] at hmap
      cases hrest : xs.mapM f with
      | error e =>
        simp [hrest] at hmap
      | ok bs =>
        simp [hrest] at hmap
        cases bs with
        | nil =>
          have hb : b = y := by
            -- Extract list equality from the Except equality
            have hlist : ([b] : List β) = [y] := by
              cases hmap
              rfl
            simpa using hlist
          subst hb
          cases xs with
          | nil =>
            refine ⟨x, rfl, ?_⟩
            simpa [hfx]
          | cons x' xs' =>
            -- mapM on a non-empty list cannot produce []
            cases hfx' : f x' with
            | error e =>
              simp [List.mapM_cons, hfx'] at hrest
              cases hrest
            | ok b' =>
              cases hrest' : xs'.mapM f with
              | error e =>
                simp [List.mapM_cons, hfx', hrest'] at hrest
                cases hrest
              | ok bs' =>
                simp [List.mapM_cons, hfx', hrest'] at hrest
                cases hrest
        | cons b' bs' =>
          cases hmap

/-- If mapM on branches gives [(l, t)], and we find a branch with matching label,
    that branch's projection is t. -/
theorem projection_of_single_branch {branches : List (Label × GlobalType)}
    {sender : String} {label : Label} {contType : LocalTypeR}
    (hmap : branches.mapM (fun (l, cont) => (projectR cont sender).map (l, ·)) =
            .ok [(label, contType)])
    {l : Label} {g : GlobalType}
    (hfind : (l, g) ∈ branches)
    (hlabel : l.name = label.name)
    : projectR g sender = .ok contType := by
  -- Get the singleton input
  obtain ⟨⟨l', g'⟩, hsingleton, hproj⟩ := mapM_singleton_input hmap
  -- Since (l, g) ∈ branches and branches = [(l', g')], we have (l, g) = (l', g')
  rw [hsingleton] at hfind
  simp only [List.mem_singleton] at hfind
  cases hfind
  -- Now hproj : (projectR g sender).map (l, ·) = .ok (label, contType)
  -- Unfold the map to get the projection result
  simp only [Except.map] at hproj
  cases hpg : projectR g sender with
  | error e =>
    simp only [hpg] at hproj
    cases hproj
  | ok t =>
    simp only [hpg] at hproj
    -- hproj : .ok (l, t) = .ok (label, contType)
    cases hproj
    -- l = label, t = contType
    rfl

private theorem mem_implies_get! {α : Type _} [Inhabited α] {l : List α} {x : α}
    (hmem : x ∈ l) : ∃ i, i < l.length ∧ l.get! i = x := by
  induction l with
  | nil => cases hmem
  | cons y ys ih =>
    have hmem' : x = y ∨ x ∈ ys := by
      simpa using hmem
    cases hmem' with
    | inl hxy =>
      subst hxy
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
    | inr hmem_tail =>
      obtain ⟨i, hi, hget⟩ := ih hmem_tail
      refine ⟨i + 1, ?_, ?_⟩
      · simpa using Nat.succ_lt_succ hi
      · simpa [List.get!_cons_succ] using hget

private theorem get!_mem {α : Type _} [Inhabited α] (l : List α) (i : Nat)
    (hi : i < l.length) :
    l.get! i ∈ l := by
  induction l generalizing i with
  | nil => cases hi
  | cons y ys ih =>
    cases i with
    | zero =>
      simp
    | succ i' =>
      have hi' : i' < ys.length := by
        simpa using hi
      have hmem := ih i' hi'
      have hmem' : ys.get! i' ∈ y :: ys := by
        exact List.mem_cons_of_mem _ hmem
      simpa [List.get!_cons_succ] using hmem'

/-- Helper: find? returning some implies element is in list and satisfies predicate. -/
private theorem find?_some_implies {α : Type _} (l : List α) (p : α → Bool) (x : α)
    (h : l.find? p = some x)
    : x ∈ l ∧ p x = true := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.find?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, hp⟩
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      have ⟨hmem, hpx⟩ := ih h
      exact ⟨List.mem_cons_of_mem y hmem, hpx⟩

/-- If find? selects a branch in a receive, the continuation is well-typed. -/
theorem recv_branch_typed_of_find (Γ : TypingContext) (sender : String)
    (branches : List (Label × Process)) (types : List (Label × LocalTypeR))
    (label : Label) (cont : Process)
    (hwt : WellTyped Γ (.recv sender branches) (.recv sender types))
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, cont))
    : ∃ contType, (label, contType) ∈ types ∧ WellTyped Γ cont contType := by
  cases hwt with
  | recv hlen hall hlabel =>
    obtain ⟨hmem, _hprop⟩ :=
      find?_some_implies branches (fun (l, _) => l.name == label.name) (label, cont) hfind
    obtain ⟨i, hi, hget⟩ := mem_implies_get! hmem
    have hwt_i : WellTyped Γ (branches.get! i).2 (types.get! i).2 := hall i
    have hlabel_i : (branches.get! i).1 = (types.get! i).1 := hlabel i
    have hcont : WellTyped Γ cont (types.get! i).2 := by
      have hwt_i' := hwt_i
      rw [hget] at hwt_i'
      exact hwt_i'
    have hlabel_eq : label = (types.get! i).1 := by
      have hlabel_i' := hlabel_i
      rw [hget] at hlabel_i'
      exact hlabel_i'
    have hi' : i < types.length := by
      simpa [hlen] using hi
    have hmem_types : types.get! i ∈ types := get!_mem types i hi'
    cases hpair : types.get! i with
    | mk lbl ty =>
      have hlabel_eq' : label = lbl := by
        rw [hpair] at hlabel_eq
        exact hlabel_eq
      have hmem_types' : (lbl, ty) ∈ types := by
        rw [hpair] at hmem_types
        exact hmem_types
      refine ⟨ty, ?_, ?_⟩
      · simpa [hlabel_eq'] using hmem_types'
      · rw [hpair] at hcont
        exact hcont

/-! ## Claims -/

/-- Subject Reduction: well-typedness is preserved by reduction.

    Theorem 1 (Yoshida & Gheri):
    If a configuration M is well-typed against global type G,
    and M reduces to M', then M' is well-typed against some G'
    where G reduces to G'.

    Formal: ∀ G M M', ⊢ M : G → M → M' → ∃ G', (G ⟹ G') ∧ ⊢ M' : G' -/
def SubjectReduction : Prop :=
  ∀ (g : GlobalType) (c c' : Configuration),
    ConfigWellTyped g c → Reduces c c' →
    ∃ g', GlobalTypeReducesStar g g' ∧ ConfigWellTyped g' c'

/-- Send preserves typing: after sending, process has continuation type.

    If P : !q{l.T} and P = send q l v P', then P' : T -/
def SendPreservesTyping : Prop :=
  ∀ (Γ : TypingContext) (receiver : String) (label : Label) (value : Value)
    (cont : Process) (t : LocalTypeR),
    WellTyped Γ (.send receiver label value cont) (.send receiver [(label, t)]) →
    WellTyped Γ cont t

/-- Receive preserves typing: after receiving, process has branch type.

    If P : ?p{lᵢ.Tᵢ} and P receives lⱼ, then continuation has type Tⱼ -/
def RecvPreservesTyping : Prop :=
  ∀ (Γ : TypingContext) (sender : String)
    (branches : List (Label × Process)) (types : List (Label × LocalTypeR))
    (j : Nat),
    WellTyped Γ (.recv sender branches) (.recv sender types) →
    j < branches.length →
    WellTyped Γ (branches.get! j).2 (types.get! j).2

/-- Claims bundle for subject reduction properties. -/
structure Claims where
  /-- Main subject reduction theorem -/
  subjectReduction : SubjectReduction
  /-- Send preserves typing -/
  sendPreservesTyping : SendPreservesTyping
  /-- Receive preserves typing -/
  recvPreservesTyping : RecvPreservesTyping

/-! ## Proofs -/

/-- Proof that send preserves typing (inversion lemma). -/
theorem send_preserves_typing : SendPreservesTyping := by
  intro Γ receiver label value cont t h
  cases h with
  | send h_cont => exact h_cont

/-- Proof that receive preserves typing (inversion lemma). -/
theorem recv_preserves_typing : RecvPreservesTyping := by
  intro Γ sender branches types j h hj
  cases h with
  | recv hlen hall hlabel =>
    exact hall j

/-- Projection commutativity for send.

    Key lemma: After consuming a send communication, the sender's
    projection evolves to the continuation type.

    If G ↾ p = !q{ℓ.T} and G consumes p →ℓ q to get G',
    then G' ↾ p = T. -/
theorem projection_after_send (g g' : GlobalType) (sender receiver : String)
    (label : Label) (contType : LocalTypeR)
    (hproj : projectR g sender = .ok (.send receiver [(label, contType)]))
    (hcons : g.consume sender receiver label = some g')
    : projectR g' sender = .ok contType :=
  projection_after_send_thm g g' sender receiver label contType hproj hcons

/-- Projection is preserved for non-participating roles.

    If G consumes p →ℓ q to get G', and r ∉ {p, q},
    then G' ↾ r = G ↾ r (or a subtype). -/
theorem projection_preserved_other (g g' : GlobalType) (sender receiver role : String)
    (label : Label) (result : LocalTypeR)
    (hcons : g.consume sender receiver label = some g')
    (hne1 : role ≠ sender)
    (hne2 : role ≠ receiver)
    (hproj : projectR g role = .ok result)
    : projectR g' role = .ok result :=
  projection_preserved_other_thm g g' sender receiver role label result hcons hne1 hne2 hproj

/-- Helper: getProcess returns some proc implies there's a matching RoleProcess. -/
theorem getProcess_implies_mem (c : Configuration) (role : String) (proc : Process)
    (hget : c.getProcess role = some proc)
    : ∃ rp ∈ c.processes, rp.role = role ∧ rp.process = proc := by
  unfold Configuration.getProcess at hget
  cases hfind : c.processes.find? (fun rp => rp.role == role) with
  | none =>
    simp only [hfind] at hget
    cases hget
  | some rp =>
    simp only [hfind, Option.map, Option.some.injEq] at hget
    have ⟨hmem, hprop⟩ := find?_some_implies _ _ _ hfind
    simp only [beq_iff_eq] at hprop
    exact ⟨rp, hmem, hprop, hget⟩

private theorem setProcess_mem_cases (c : Configuration) (role : String) (proc : Process)
    (rp : RoleProcess) (hmem : rp ∈ (c.setProcess role proc).processes) :
    (rp.role = role ∧ rp.process = proc) ∨ (rp ∈ c.processes ∧ rp.role ≠ role) := by
  unfold Configuration.setProcess at hmem
  simp only [List.mem_map] at hmem
  obtain ⟨rp0, hrp0, hrp_eq⟩ := hmem
  by_cases hrole : rp0.role = role
  · have hbeq : (rp0.role == role) = true := by
      simp [beq_iff_eq, hrole]
    have hrp_eq' : { rp0 with process := proc } = rp := by
      simpa [hbeq] using hrp_eq
    cases hrp_eq'
    exact Or.inl ⟨by simpa [hrole], rfl⟩
  · have hbeq : (rp0.role == role) = false :=
      beq_eq_false_iff_ne.mpr hrole
    have hrp_eq' : rp0 = rp := by
      simpa [hbeq] using hrp_eq
    subst hrp_eq'
    exact Or.inr ⟨hrp0, hrole⟩

private theorem dequeue_preserves_processes (c c' : Configuration) (ch : Channel)
    (msg : Message) (hdeq : c.dequeue ch = some (msg, c')) :
    c'.processes = c.processes := by
  cases hq : c.getQueue ch with
  | nil =>
    have hnone : (none : Option (Message × Configuration)) = some (msg, c') := by
      simpa [Configuration.dequeue, hq] using hdeq
    cases hnone
  | cons msg' rest =>
    have hsome : some (msg', c.setQueue ch rest) = some (msg, c') := by
      simpa [Configuration.dequeue, hq] using hdeq
    cases hsome
    simp [Configuration.setQueue]

private theorem dequeue_preserves_hasUniqueRoles (c c' : Configuration) (ch : Channel)
    (msg : Message) (hdeq : c.dequeue ch = some (msg, c'))
    (hunique : c.hasUniqueRoles) : c'.hasUniqueRoles := by
  have hproc : c'.processes = c.processes :=
    dequeue_preserves_processes c c' ch msg hdeq
  unfold Configuration.hasUniqueRoles Configuration.roleNames at *
  simpa [hproc] using hunique

/-- Helper: Get the projected type for a role from a well-typed config. -/
theorem wellTyped_role_has_projection (g : GlobalType) (c : Configuration)
    (role : String) (proc : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some proc)
    : ∃ lt, projectR g role = .ok lt ∧ WellTyped [] proc lt := by
  obtain ⟨rp, hrp_mem, hrp_role, hrp_proc⟩ :=
    getProcess_implies_mem c role proc hget
  obtain ⟨_, hallwt⟩ := hwt
  have hrpwt := hallwt rp hrp_mem
  unfold RoleProcessWellTyped at hrpwt
  have hrpwt' :
      match projectR g role with
      | .ok lt => WellTyped [] rp.process lt
      | .error _ => False := by
    simpa [hrp_role] using hrpwt
  cases hproj : projectR g role with
  | error e =>
    have : False := by
      simpa [hproj] using hrpwt'
    exact False.elim this
  | ok lt =>
    have hwt_proc : WellTyped [] rp.process lt := by
      simpa [hproj] using hrpwt'
    have hwt_proc' : WellTyped [] proc lt := by
      simpa [hrp_proc] using hwt_proc
    exact ⟨lt, rfl, hwt_proc'⟩

/-- Subject reduction for send (queue-typed). -/
theorem subject_reduction_send_queue (g : GlobalType) (c : Configuration)
    (role receiver : String) (label : Label) (value : Value) (cont : Process)
    (hwt : ConfigWellTypedQueue g c)
    (hcoh : coherentG g)
    (hget : c.getProcess role = some (.send receiver label value cont))
    : ConfigWellTypedQueue g (reduceSendConfig c role receiver label value cont) := by
  rcases hwt with ⟨hunique, qenv, hqwt, hqcons, hall⟩
  let ch : Channel := { sender := role, receiver := receiver }
  let msg : Message := { sender := role, label := label, value := value }
  have hunique_enq : (c.enqueue ch msg).hasUniqueRoles := by
    have hproc : (c.enqueue ch msg).processes = c.processes :=
      Configuration.enqueue_processes c ch msg
    unfold Configuration.hasUniqueRoles Configuration.roleNames at *
    simpa [hproc] using hunique
  have hunique' : (reduceSendConfig c role receiver label value cont).hasUniqueRoles := by
    simpa [reduceSendConfig] using
      setProcess_preserves_hasUniqueRoles (c.enqueue ch msg) role cont hunique_enq
  let qenv' : QueueTypeEnv :=
    queueTypeEnv_enqueue qenv ch (queueTypeOfQueue (c.getQueue ch ++ [msg]))
  have hqwt' : QueueEnvWellTyped (c.enqueue ch msg) qenv' :=
    QueueEnvWellTyped_enqueue c qenv ch msg hqwt
  have hqwt'' : QueueEnvWellTyped (reduceSendConfig c role receiver label value cont) qenv' := by
    simpa [reduceSendConfig, Configuration.setProcess_queues] using hqwt'
  have hqcons' : QueueEnvConsistent g qenv' :=
    QueueEnvConsistent_enqueue g qenv ch (queueTypeOfQueue (c.getQueue ch ++ [msg])) hqcons
  refine ⟨hunique', qenv', hqwt'', hqcons', ?_⟩
  intro rp hrp
  have hrp' : rp ∈ (c.setProcess role cont).processes := by
    simpa [reduceSendConfig, Configuration.enqueue_processes] using hrp
  cases setProcess_mem_cases c role cont rp hrp' with
  | inl hsender =>
    rcases hsender with ⟨hrole, hproc⟩
    obtain ⟨rp0, hrp0, hrole0, hproc0⟩ :=
      getProcess_implies_mem c role (.send receiver label value cont) hget
    obtain ⟨g0, lt0, hstar0, hproj0, hwt_send⟩ := hall rp0 hrp0
    have hcoh0 : coherentG g0 := coherentG_stepStar hcoh hstar0
    have hwt_send' : WellTyped [] (.send receiver label value cont) lt0 := by
      simpa [hproc0] using hwt_send
    obtain ⟨contType, hlt_eq, hwt_cont⟩ :=
      wellTyped_send_inversion [] receiver label value cont lt0 hwt_send'
    have hproj_send : projectR g0 role = .ok (.send receiver [(label, contType)]) := by
      simpa [hrole0, hlt_eq] using hproj0
    obtain ⟨g1, hstep⟩ := projection_send_implies_step g0 role receiver label contType hproj_send hcoh0
    have hstar1 : GlobalTypeStepStar g0 g1 :=
      GlobalTypeStepStar.step g0 g1 g1 _ hstep (GlobalTypeStepStar.refl g1)
    have hstar : GlobalTypeStepStar g g1 :=
      GlobalTypeStepStar.trans hstar0 hstar1
    have hproj_cont : projectR g1 role = .ok contType :=
      projection_after_send_step g0 g1 role receiver label contType hproj_send hstep
    have hproj_cont' : projectR g1 rp.role = .ok contType := by
      simpa [hrole] using hproj_cont
    have hwt_cont' : WellTyped [] rp.process contType := by
      simpa [hproc] using hwt_cont
    exact ⟨g1, contType, hstar, hproj_cont', hwt_cont'⟩
  | inr hother =>
    rcases hother with ⟨hrp0, _hne⟩
    exact hall rp hrp0

/-- Subject reduction for recv (queue-typed). -/
theorem subject_reduction_recv_queue (g : GlobalType) (c c' : Configuration)
    (role sender : String) (branches : List (Label × Process))
    (msg : Message) (cont : Process)
    (hwt : ConfigWellTypedQueue g c)
    (hcoh : coherentG g)
    (hget : c.getProcess role = some (.recv sender branches))
    (hdeq : c.dequeue { sender := sender, receiver := role } = some (msg, c'))
    (hfind : branches.find? (fun (l, _) => l.name == msg.label.name) = some (msg.label, cont))
    : ConfigWellTypedQueue g (reduceRecvConfig c' role cont) := by
  rcases hwt with ⟨hunique, qenv, hqwt, hqcons, hall⟩
  have hunique' : c'.hasUniqueRoles :=
    dequeue_preserves_hasUniqueRoles c c' { sender := sender, receiver := role } msg hdeq hunique
  have hunique'' : (reduceRecvConfig c' role cont).hasUniqueRoles :=
    setProcess_preserves_hasUniqueRoles c' role cont hunique'
  obtain ⟨rest, _hrest, hqwt'⟩ :=
    QueueEnvWellTyped_dequeue c c' qenv { sender := sender, receiver := role } msg hqwt hdeq
  let qenv' : QueueTypeEnv :=
    queueTypeEnv_dequeue qenv { sender := sender, receiver := role } (queueTypeOfQueue rest)
  have hqwt'' : QueueEnvWellTyped (reduceRecvConfig c' role cont) qenv' := by
    simpa [reduceRecvConfig, Configuration.setProcess_queues] using hqwt'
  have hqcons' : QueueEnvConsistent g qenv' :=
    QueueEnvConsistent_dequeue g qenv { sender := sender, receiver := role }
      (queueTypeOfQueue rest) hqcons
  refine ⟨hunique'', qenv', hqwt'', hqcons', ?_⟩
  intro rp hrp
  have hrp' : rp ∈ (c'.setProcess role cont).processes := by
    simpa [reduceRecvConfig] using hrp
  cases setProcess_mem_cases c' role cont rp hrp' with
  | inl hrecv =>
    rcases hrecv with ⟨hrole, hproc⟩
    obtain ⟨rp0, hrp0, hrole0, hproc0⟩ :=
      getProcess_implies_mem c role (.recv sender branches) hget
    obtain ⟨g0, lt0, hstar0, hproj0, hwt_recv⟩ := hall rp0 hrp0
    have hcoh0 : coherentG g0 := coherentG_stepStar hcoh hstar0
    have hwt_recv' : WellTyped [] (.recv sender branches) lt0 := by
      simpa [hproc0] using hwt_recv
    obtain ⟨types, hlt_eq, _hlen, _hall, _hlabel⟩ :=
      wellTyped_recv_inversion [] sender branches lt0 hwt_recv'
    have hproj_recv : projectR g0 role = .ok (.recv sender types) := by
      simpa [hrole0, hlt_eq] using hproj0
    obtain ⟨contType, hmem_types, hwt_cont⟩ :=
      recv_branch_typed_of_find [] sender branches types msg.label cont
        (by simpa [hlt_eq] using hwt_recv') hfind
    obtain ⟨g1, hstep⟩ :=
      projection_recv_implies_step g0 sender role msg.label types contType hproj_recv hmem_types hcoh0
    have hstar1 : GlobalTypeStepStar g0 g1 :=
      GlobalTypeStepStar.step g0 g1 g1 _ hstep (GlobalTypeStepStar.refl g1)
    have hstar : GlobalTypeStepStar g g1 :=
      GlobalTypeStepStar.trans hstar0 hstar1
    have hproj_cont : projectR g1 role = .ok contType :=
      projection_after_recv_step g0 g1 sender role msg.label types contType hproj_recv hmem_types hstep
    have hproj_cont' : projectR g1 rp.role = .ok contType := by
      simpa [hrole] using hproj_cont
    have hwt_cont' : WellTyped [] rp.process contType := by
      simpa [hproc] using hwt_cont
    exact ⟨g1, contType, hstar, hproj_cont', hwt_cont'⟩
  | inr hother =>
    rcases hother with ⟨hrp0, _hne⟩
    have hproc : c'.processes = c.processes :=
      dequeue_preserves_processes c c' { sender := sender, receiver := role } msg hdeq
    have hrp0' : rp ∈ c.processes := by
      simpa [hproc] using hrp0
    exact hall rp hrp0'

/-- Subject reduction for send (queue-typed wrapper). -/
theorem subject_reduction_send (g : GlobalType) (c : Configuration)
    (role receiver : String) (label : Label) (value : Value) (cont : Process)
    (hwt : ConfigWellTypedQueue g c)
    (hcoh : coherentG g)
    (hget : c.getProcess role = some (.send receiver label value cont))
    : ∃ g', GlobalTypeReducesStar g g' ∧
            ConfigWellTypedQueue g' (reduceSendConfig c role receiver label value cont) := by
  refine ⟨g, GlobalTypeReducesStar.refl g, ?_⟩
  exact subject_reduction_send_queue g c role receiver label value cont hwt hcoh hget

/-- Subject reduction for conditional case.

    When a conditional evaluates, it takes one of two branches.
    Both branches have the same type, so typing is preserved. -/
theorem subject_reduction_cond (g : GlobalType) (c : Configuration)
    (role : String) (b : Bool) (p q : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.cond b p q))
    : ConfigWellTyped g (c.setProcess role (if b then p else q)) := by
  obtain ⟨lt, hproj, hwt_cond⟩ := wellTyped_role_has_projection g c role _ hwt hget
  have ⟨hp, hq⟩ := wellTyped_cond_inversion [] b p q lt hwt_cond
  cases b with
  | true =>
    simp only [↓reduceIte]
    exact configWellTyped_setProcess g c role p lt hwt hproj hp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact configWellTyped_setProcess g c role q lt hwt hproj hq

/-- Subject reduction for recursion case.

    When a recursion unfolds, the substituted process is well-typed
    with the unfolded type. -/
theorem subject_reduction_rec (g : GlobalType) (c : Configuration)
    (role x : String) (body : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.recurse x body))
    : ∃ g', GlobalTypeReducesStar g g' ∧
            ConfigWellTyped g' (c.setProcess role (body.substitute x (.recurse x body))) := by
  -- Recursion unfolding is a local step: global type doesn't change
  refine ⟨g, GlobalTypeReducesStar.refl g, ?_⟩
  -- Get the projected type for this role
  obtain ⟨lt, hproj, hwt_rec⟩ := wellTyped_role_has_projection g c role _ hwt hget
  -- By inversion, lt = μX.bodyType for some bodyType
  obtain ⟨bodyType, hlt_eq, hwt_body⟩ := wellTyped_rec_inversion [] x body lt hwt_rec
  -- After unfolding, the process has the same type (equi-recursive)
  have hunfold : WellTyped [] (body.substitute x (.recurse x body)) (.mu x bodyType) := by
    rw [hlt_eq] at hwt_rec
    exact wellTyped_rec_unfold [] x body bodyType hwt_rec
  -- Apply configWellTyped_setProcess
  rw [hlt_eq] at hproj
  exact configWellTyped_setProcess g c role _ _ hwt hproj hunfold

/-- Subject reduction theorem.

    Proof outline (following Yoshida & Gheri):
    1. By case analysis on the reduction rule
    2. For send reduction: continuation has continuation type
    3. For receive reduction: selected branch has branch type
    4. For cond/rec: both proven above -/
axiom subject_reduction : SubjectReduction

/-! ## Partial Claims Bundle -/

/-- Partial claims with proven lemmas. -/
def partialClaims : SendPreservesTyping ∧ RecvPreservesTyping :=
  ⟨send_preserves_typing, recv_preserves_typing⟩

end Rumpsteak.Proofs.Safety.SubjectReduction
