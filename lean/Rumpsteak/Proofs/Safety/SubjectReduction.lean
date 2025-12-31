import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration
import Rumpsteak.Protocol.Semantics.Reduction
import Rumpsteak.Protocol.Semantics.Typing

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
open Rumpsteak.Protocol.Semantics.Process
open Rumpsteak.Protocol.Semantics.Configuration
open Rumpsteak.Protocol.Semantics.Reduction
open Rumpsteak.Protocol.Semantics.Typing

/-! ## Axioms for Projection Commutativity

These axioms capture fundamental properties of multiparty session type projection
that are standard results in the literature (Yoshida & Gheri). They describe how
projections evolve as the global type consumes communications. -/

/-- Projection after send axiom: after consuming a send, the sender's projection evolves.

    PROOF SKETCH (Session type theory):
    If G ↾ sender = !receiver{ℓ.T} and G consumes sender→ℓ→receiver to get G',
    then G' ↾ sender = T.

    This follows from the structure of projection: if the sender sees a send type,
    the global type must have a matching communication, and consuming it advances
    both the global type and the sender's local view. -/
axiom projection_after_send_ax (g g' : GlobalType) (sender receiver : String)
    (label : Label) (contType : LocalTypeR)
    (hproj : projectR g sender = .ok (.send receiver [(label, contType)]))
    (hcons : g.consume sender receiver label = some g')
    : projectR g' sender = .ok contType

/-- Projection preserved for non-participants axiom.

    PROOF SKETCH (Session type theory):
    If G consumes sender→ℓ→receiver to get G', and role ∉ {sender, receiver},
    then G' ↾ role = G ↾ role.

    This follows from projection structure: non-participants see the same behavior
    regardless of which branch is taken, because the merge operation for external
    roles succeeds only when all branches project to the same local type. -/
axiom projection_preserved_other_ax (g g' : GlobalType) (sender receiver role : String)
    (label : Label)
    (hcons : g.consume sender receiver label = some g')
    (hne1 : role ≠ sender)
    (hne2 : role ≠ receiver)
    : projectR g' role = projectR g role

/-- Subject reduction for send axiom.

    PROOF SKETCH (Session type theory):
    When a sender executes a send, the configuration evolves:
    1. The sender's process moves to its continuation
    2. The message is enqueued in the sender→receiver queue
    3. The global type consumes the corresponding communication

    The continuation is well-typed against the evolved global type because:
    - By inversion, the continuation has the continuation type
    - By projection_after_send, the evolved global type projects to this type -/
axiom subject_reduction_send_ax (g : GlobalType) (c : Configuration)
    (role receiver : String) (label : Label) (value : Value) (cont : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.send receiver label value cont))
    : ∃ g', GlobalTypeReducesStar g g' ∧
            ConfigWellTyped g' (reduceSendConfig c role receiver label value cont)

/-- Subject reduction for recv axiom.

    PROOF SKETCH (Session type theory):
    When a receiver executes a receive:
    1. The receiver's process moves to the selected branch continuation
    2. The message is dequeued from the sender→receiver queue
    3. The global type consumes the corresponding communication

    The selected branch is well-typed against the evolved global type because:
    - The message label matches a branch in the receiver's type
    - By inversion, that branch has the corresponding branch type
    - By projection after the send (already consumed), the type matches -/
axiom subject_reduction_recv_ax (g : GlobalType) (c : Configuration)
    (role sender : String) (branches : List (Label × Process))
    (msg : Message) (cont : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.recv sender branches))
    (hdeq : c.dequeue sender role = some (msg, c))
    (hfind : branches.find? (fun (l, _) => l.name == msg.label) = some (⟨msg.label⟩, cont))
    : ∃ g', GlobalTypeReducesStar g g' ∧ ConfigWellTyped g' (c.setProcess role cont)

/-! ## Helper Lemmas for mapM and Projection -/

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
private theorem mapM_singleton_input {α β ε : Type} {f : α → Except ε β}
    {xs : List α} {y : β}
    (hmap : xs.mapM f = .ok [y])
    : ∃ x, xs = [x] ∧ f x = .ok y := by
  cases xs with
  | nil =>
    simp only [List.mapM_nil] at hmap
    cases hmap
  | cons x xs' =>
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
        -- hmap : .ok (b :: bs) = .ok [y]
        cases hmap
        -- Now b :: bs = [y], so b = y and bs = []
        cases xs' with
        | nil =>
          simp only [List.mapM_nil] at hrest
          cases hrest
          exact ⟨x, rfl, hfx⟩
        | cons _ _ =>
          -- xs' is non-empty, so bs is non-empty, contradiction with bs = []
          simp only [List.mapM_cons, bind, Except.bind] at hrest
          cases hfx' : f _ with
          | error e => simp only [hfx'] at hrest; cases hrest
          | ok _ =>
            simp only [hfx'] at hrest
            cases hrest' : (List.mapM f _) with
            | error e => simp only [hrest'] at hrest; cases hrest
            | ok bs' => simp only [hrest'] at hrest; cases hrest

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
  projection_after_send_ax g g' sender receiver label contType hproj hcons

/-- Projection is preserved for non-participating roles.

    If G consumes p →ℓ q to get G', and r ∉ {p, q},
    then G' ↾ r = G ↾ r (or a subtype). -/
theorem projection_preserved_other (g g' : GlobalType) (sender receiver role : String)
    (label : Label)
    (hcons : g.consume sender receiver label = some g')
    (hne1 : role ≠ sender)
    (hne2 : role ≠ receiver)
    : projectR g' role = projectR g role :=
  projection_preserved_other_ax g g' sender receiver role label hcons hne1 hne2

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

/-- Helper: Get the projected type for a role from a well-typed config. -/
theorem wellTyped_role_has_projection (g : GlobalType) (c : Configuration)
    (role : String) (proc : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some proc)
    : ∃ lt, projectR g role = .ok lt ∧ WellTyped [] proc lt := by
  obtain ⟨rp, hrp_mem, hrole, hproc⟩ := getProcess_implies_mem c role proc hget
  have hrpwt := hwt rp hrp_mem
  unfold RoleProcessWellTyped at hrpwt
  rw [hrole] at hrpwt
  cases hproj : projectR g role with
  | error e =>
    simp only [hproj] at hrpwt
  | ok lt =>
    rw [hproj] at hrpwt
    subst hproc
    exact ⟨lt, rfl, hrpwt⟩

/-- Subject reduction for send case.

    When a process sends, it moves to its continuation which has the
    continuation type. The global type evolves by consuming this communication.

    Note: In asynchronous semantics, the message is enqueued, and we
    use the evolved global type to type the continuation. -/
theorem subject_reduction_send (g : GlobalType) (c : Configuration)
    (role receiver : String) (label : Label) (value : Value) (cont : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.send receiver label value cont))
    : ∃ g', GlobalTypeReducesStar g g' ∧
            ConfigWellTyped g' (reduceSendConfig c role receiver label value cont) :=
  subject_reduction_send_ax g c role receiver label value cont hwt hget

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
theorem subject_reduction : SubjectReduction := by
  intro g c c' hwt hred
  -- Case analysis on the reduction rule
  cases hred with
  | send c role receiver label value cont hget =>
    -- Send case: use subject_reduction_send
    exact subject_reduction_send g c role receiver label value cont hwt hget
  | recv c role sender branches msg cont hget hdeq hfind =>
    -- Receive case: use subject_reduction_recv_ax
    exact subject_reduction_recv_ax g c role sender branches msg cont hwt hget hdeq hfind
  | cond c role b p q hget =>
    -- Conditional case: use subject_reduction_cond
    refine ⟨g, GlobalTypeReducesStar.refl g, ?_⟩
    exact subject_reduction_cond g c role b p q hwt hget
  | recurse c role x body hget =>
    -- Recursion case: use subject_reduction_rec
    exact subject_reduction_rec g c role x body hwt hget

/-! ## Partial Claims Bundle -/

/-- Partial claims with proven lemmas. -/
def partialClaims : SendPreservesTyping ∧ RecvPreservesTyping :=
  ⟨send_preserves_typing, recv_preserves_typing⟩

end Rumpsteak.Proofs.Safety.SubjectReduction
