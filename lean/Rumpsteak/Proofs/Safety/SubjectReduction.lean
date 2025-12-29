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

import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Rumpsteak.Protocol.ProjectionR
import Rumpsteak.Protocol.Semantics.Process
import Rumpsteak.Protocol.Semantics.Configuration
import Rumpsteak.Protocol.Semantics.Reduction
import Rumpsteak.Protocol.Semantics.Typing

namespace Rumpsteak.Proofs.Safety.SubjectReduction

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR
open Rumpsteak.Protocol.ProjectionR
open Rumpsteak.Protocol.Semantics.Process
open Rumpsteak.Protocol.Semantics.Configuration
open Rumpsteak.Protocol.Semantics.Reduction
open Rumpsteak.Protocol.Semantics.Typing

/-! ## Helper Lemmas for mapM and Projection -/

/-- If mapM succeeds on a list and produces a list containing (l, t),
    then there was an input (l, g) where f(l, g) = (l, t). -/
theorem mapM_result_member {α β : Type} {f : α → Except ε β}
    {xs : List α} {ys : List β} {y : β}
    (hmap : xs.mapM f = .ok ys) (hmem : y ∈ ys)
    : ∃ x ∈ xs, f x = .ok y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Except.pure_def, Except.ok.injEq] at hmap
    subst hmap
    simp only [List.not_mem_nil] at hmem
  | cons x xs ih =>
    simp only [List.mapM_cons, Except.bind_eq_ok] at hmap
    obtain ⟨y', hy', ys', hys', heq⟩ := hmap
    subst heq
    simp only [List.mem_cons] at hmem
    cases hmem with
    | inl h =>
      subst h
      exact ⟨x, List.mem_cons_self x xs, hy'⟩
    | inr h =>
      obtain ⟨x', hx', hfx'⟩ := ih hys' h
      exact ⟨x', List.mem_cons_of_mem x hx', hfx'⟩

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
  -- If mapM gives a single result [(label, contType)], the input had one branch
  -- and that branch projects to contType
  cases branches with
  | nil =>
    simp only [List.not_mem_nil] at hfind
  | cons b bs =>
    simp only [List.mapM_cons, Except.bind_eq_ok] at hmap
    obtain ⟨pt, hpt, pts, hpts, heq⟩ := hmap
    simp only [Except.map_eq_ok_iff] at hpt
    obtain ⟨lt, hlt, heq_pt⟩ := hpt
    simp only [List.mem_cons] at hfind
    cases hfind with
    | inl h =>
      -- The first branch
      obtain ⟨l', g'⟩ := b
      simp only [Prod.mk.injEq] at h heq_pt
      obtain ⟨hl, hg⟩ := h
      subst hl hg
      simp only at heq_pt heq hlt
      simp only [Except.pure_def, Except.ok.injEq, List.cons.injEq] at heq
      obtain ⟨heq1, heq2⟩ := heq
      simp only [Prod.mk.injEq] at heq1
      obtain ⟨_, heq_lt⟩ := heq1
      rw [← heq_lt, hlt]
    | inr h =>
      -- A later branch - but we only have one result, so bs must be empty
      simp only [Except.pure_def, Except.ok.injEq, List.cons.injEq] at heq
      obtain ⟨_, heq2⟩ := heq
      -- pts = [] means bs was empty after mapM
      simp only [List.eq_nil_iff_forall_not_mem] at heq2
      -- But if b' ∈ bs, then mapM would give a non-empty pts
      cases bs with
      | nil => simp only [List.not_mem_nil] at h
      | cons b' bs' =>
        simp only [List.mapM_cons, Except.bind_eq_ok] at hpts
        obtain ⟨pt', hpt', pts', hpts', heq'⟩ := hpts
        simp only [Except.pure_def, Except.ok.injEq] at heq'
        subst heq'
        exact absurd (List.mem_cons_self pt' pts') (heq2 pt')

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
    : projectR g' sender = .ok contType := by
  -- Case analysis on the global type
  -- The projection to sender giving a send type means g must be a comm from sender
  cases g with
  | «end» =>
    -- end doesn't project to send
    simp only [projectR] at hproj
  | var t =>
    -- var doesn't project to send (projects to var)
    simp only [projectR, Except.pure_def] at hproj
  | comm s r branches =>
    -- This is the main case: g = comm s r branches
    simp only [projectR] at hproj
    split_ifs at hproj with hbranches hsender hreceiver
    · -- Empty branches case
      simp only [Except.bind_err] at hproj
    · -- sender is the sender role (s = sender)
      -- The projection gives !r{projBranches}
      -- So receiver = r and the branches project accordingly
      simp only [GlobalType.consume] at hcons
      rw [← hsender] at hcons
      simp only [beq_self_eq_true, true_and] at hcons
      by_cases hrr : r == receiver
      · simp only [hrr, ↓reduceIte] at hcons
        -- hcons says g' is the continuation from the matching branch
        -- hproj says projecting branches gives [(label, contType)]
        -- So projecting g' should give contType
        cases hproj_branches : branches.mapM (fun (l, cont) => (projectR cont sender).map (l, ·)) with
        | error e =>
          simp only [hproj_branches, Except.bind_err] at hproj
        | ok projBranches =>
          simp only [hproj_branches, Except.bind_ok, Except.pure_def, Except.ok.injEq] at hproj
          -- hproj gives us the structure: projBranches = [(label, contType)] when receiver = r
          -- Actually hproj says .send receiver projBranches = .send receiver [(label, contType)]
          -- So if the list length matches, we have one branch
          -- The g' is the continuation from the matching branch
          simp only [Option.map_eq_some_iff] at hcons
          obtain ⟨⟨l, cont⟩, hfind, hcont⟩ := hcons
          simp only at hcont
          subst hcont
          -- Now we need to show projectR cont sender = contType
          -- The mapM over branches with (label, contType) result means
          -- projectR cont sender = contType for the matching branch
          simp only [beq_iff_eq] at hrr
          subst hrr
          -- hproj : .send receiver projBranches = .send receiver [(label, contType)]
          -- So projBranches = [(label, contType)]
          simp only [LocalTypeR.send.injEq] at hproj
          obtain ⟨_, hprojBranches⟩ := hproj
          -- Now use projection_of_single_branch
          -- hfind gives us that (l, cont) is found in branches
          have hmem : (l, cont) ∈ branches := List.mem_of_find?_eq_some hfind
          -- And l.name == label.name from the find? predicate
          simp only [List.find?_eq_some_iff] at hfind
          obtain ⟨_, _, hlabel_match, _⟩ := hfind
          simp only [beq_iff_eq] at hlabel_match
          rw [← hprojBranches] at hproj_branches
          exact projection_of_single_branch hproj_branches hmem hlabel_match
      · -- receiver doesn't match, hcons fails
        simp only [hrr, ↓reduceIte, Option.map_eq_some_iff] at hcons
        -- hcons is now False since find? returns none (no match) - this is a false case
        -- Actually, with hrr false, the consumption still might find a branch
        -- But wait, the consume function checks s == sender && r == receiver
        -- Since hsender is true (s = sender) but hrr is false (r ≠ receiver),
        -- the condition fails and consume returns none
        simp only [GlobalType.consume] at hcons
        rw [← hsender] at hcons
        simp only [beq_self_eq_true, true_and, hrr, ↓reduceIte] at hcons
    · -- sender is the receiver role (sender = r)
      -- For hcons to succeed, we need s == sender && r == receiver
      -- But here sender = r (hreceiver), so s == sender means s == r
      -- Also r == receiver means sender == receiver (since sender = r)
      -- The projection gives recv type, not send type
      simp only [GlobalType.consume] at hcons
      -- hcons requires s == sender, but sender = r and s ≠ r (distinct roles in protocol)
      -- Actually, we can't assume s ≠ r from the global type directly
      -- Let's check what hcons becomes
      by_cases hss : s == sender
      · simp only [hss, true_and] at hcons
        by_cases hrr : r == receiver
        · simp only [hrr, ↓reduceIte, Option.map_eq_some_iff] at hcons
          -- This would mean s = sender and r = receiver
          -- But hreceiver says sender = r, so sender = receiver
          -- And s = sender, so s = receiver = r
          -- So we'd have s = r, which means self-communication
          -- The projection to sender = r gives recv type, but hproj says send type
          cases hproj_branches : branches.mapM (fun (l, cont) => (projectR cont sender).map (l, ·)) with
          | error e =>
            simp only [hproj_branches, Except.bind_err] at hproj
          | ok projBranches =>
            simp only [hproj_branches, Except.bind_ok, Except.pure_def] at hproj
            -- hproj says it's a recv type since sender = r (the receiver)
            -- But our goal is that hproj is .send, so this should be a contradiction
            -- However hreceiver means sender = r, so projection gives .recv s _
            -- which contradicts hproj being .send receiver _
        · simp only [hrr, ↓reduceIte] at hcons
      · simp only [hss, false_and, ↓reduceIte] at hcons
    · -- sender is neither sender nor receiver (s ≠ sender ∧ r ≠ sender)
      -- For hcons to succeed, we need s == sender, but here s ≠ sender
      simp only [GlobalType.consume] at hcons
      simp only [bne_iff_ne, ne_eq, beq_eq_false_iff_ne] at hsender hreceiver
      have hss : (s == sender) = false := by simp only [beq_eq_false_iff_ne]; exact hsender
      simp only [hss, false_and, ↓reduceIte] at hcons
  | rec t body =>
    -- Recursion case: unfold and apply recursively
    simp only [GlobalType.consume] at hcons
    -- g.consume unfolds to (body.substitute t g).consume
    -- Need to apply IH on the unfolded type
    sorry

/-- Projection is preserved for non-participating roles.

    If G consumes p →ℓ q to get G', and r ∉ {p, q},
    then G' ↾ r = G ↾ r (or a subtype). -/
theorem projection_preserved_other (g g' : GlobalType) (sender receiver role : String)
    (label : Label)
    (hcons : g.consume sender receiver label = some g')
    (hne1 : role ≠ sender)
    (hne2 : role ≠ receiver)
    : projectR g' role = projectR g role := by
  -- Non-participants have unchanged projections
  sorry

/-- Helper: Get the projected type for a role from a well-typed config. -/
theorem wellTyped_role_has_projection (g : GlobalType) (c : Configuration)
    (role : String) (proc : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some proc)
    : ∃ lt, projectR g role = .ok lt ∧ WellTyped [] proc lt := by
  unfold ConfigWellTyped at hwt
  unfold RoleProcessWellTyped at hwt
  simp only [List.all_eq_true, decide_eq_true_eq] at hwt
  unfold Configuration.getProcess at hget
  simp only [Option.map_eq_some_iff] at hget
  obtain ⟨rp, hrp, hproc⟩ := hget
  have hwt_rp := hwt rp hrp
  cases hproj : projectR g rp.role with
  | ok lt =>
    simp only [hproj] at hwt_rp
    simp only [← hproc]
    exact ⟨lt, hproj, hwt_rp⟩
  | error _ =>
    simp only [hproj] at hwt_rp

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
            ConfigWellTyped g' (Reduces.reduceSendConfig c role receiver label value cont) := by
  -- Get the typing for the sender
  obtain ⟨lt, hproj, hwt_proc⟩ := wellTyped_role_has_projection g c role _ hwt hget
  -- By inversion on send typing
  obtain ⟨contType, heq, hwt_cont⟩ := wellTyped_send_inversion [] receiver label value cont lt hwt_proc
  -- The global type should evolve by consuming this send
  -- If g.consume role receiver label = some g', then:
  -- - projectR g' role = contType (sender continues with continuation type)
  -- - For other roles, projections are preserved or subtyped
  cases hcons : g.consume role receiver label with
  | none =>
    -- If consumption fails, we use the same global type with sorry
    -- This case needs more sophisticated handling
    use g
    constructor
    · exact GlobalTypeReducesStar.refl g
    · sorry
  | some g' =>
    use g'
    constructor
    · -- g reduces to g' in one step
      exact GlobalTypeReducesStar.step g g' g'
        (GlobalTypeReduces.comm role receiver _ label g' (by
          -- Need to show branches.find? ... = some (label, g')
          -- This follows from hcons
          sorry))
        (GlobalTypeReducesStar.refl g')
    · -- The reduced config is well-typed against g'
      unfold Reduces.reduceSendConfig
      -- After enqueue, processes are unchanged
      -- After setProcess, the sender has the continuation type
      -- By projection_after_send, projectR g' role = contType
      have hproj' : projectR g' role = .ok contType := by
        rw [heq] at hproj
        exact projection_after_send g g' role receiver label contType hproj hcons
      -- Now use configWellTyped_setProcess
      -- But we also need to handle the enqueue and other roles
      sorry

/-- Subject reduction for conditional case.

    When a conditional evaluates, it takes one of two branches.
    Both branches have the same type, so typing is preserved. -/
theorem subject_reduction_cond (g : GlobalType) (c : Configuration)
    (role : String) (b : Bool) (p q : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.cond b p q))
    : ConfigWellTyped g (c.setProcess role (if b then p else q)) := by
  obtain ⟨lt, hproj, hwt_proc⟩ := wellTyped_role_has_projection g c role _ hwt hget
  obtain ⟨hwt_p, hwt_q⟩ := wellTyped_cond_inversion [] b p q lt hwt_proc
  cases b with
  | true =>
    simp only [↓reduceIte]
    exact configWellTyped_setProcess g c role p lt hwt hproj hwt_p
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact configWellTyped_setProcess g c role q lt hwt hproj hwt_q

/-- Subject reduction for recursion case.

    When a recursion unfolds, the substituted process is well-typed
    with the unfolded type. -/
theorem subject_reduction_rec (g : GlobalType) (c : Configuration)
    (role x : String) (body : Process)
    (hwt : ConfigWellTyped g c)
    (hget : c.getProcess role = some (.rec x body))
    : ∃ g', GlobalTypeReducesStar g g' ∧
            ConfigWellTyped g' (c.setProcess role (body.substitute x (.rec x body))) := by
  obtain ⟨lt, hproj, hwt_proc⟩ := wellTyped_role_has_projection g c role _ hwt hget
  obtain ⟨bodyType, heq, hwt_body⟩ := wellTyped_rec_inversion [] x body lt hwt_proc
  use g
  constructor
  · exact GlobalTypeReducesStar.refl g
  · -- The unfolded process has the recursive type (equi-recursive)
    have hwt_unfold := wellTyped_rec_unfold [] x body bodyType hwt_proc
    -- Now use configWellTyped_setProcess
    rw [heq] at hproj
    exact configWellTyped_setProcess g c role _ (.rec x bodyType) hwt hproj hwt_unfold

/-- Subject reduction theorem.

    Proof outline (following Yoshida & Gheri):
    1. By case analysis on the reduction rule
    2. For send reduction: continuation has continuation type
    3. For receive reduction: selected branch has branch type
    4. For cond/rec: both proven above -/
theorem subject_reduction : SubjectReduction := by
  intro g c c' hwt hred
  cases hred with
  | send c role receiver label value cont hget =>
    exact subject_reduction_send g c role receiver label value cont hwt hget

  | recv c role sender branches msg cont hget hdeq hfind =>
    -- Receive case: select the matching branch
    use g
    constructor
    · exact GlobalTypeReducesStar.refl g
    · -- Need to show the selected continuation is well-typed
      obtain ⟨lt, hproj, hwt_proc⟩ := wellTyped_role_has_projection g c role _ hwt hget
      obtain ⟨types, heq, hlen, hall, hlabel⟩ := wellTyped_recv_inversion [] sender branches lt hwt_proc
      -- The selected continuation has the matching type
      sorry

  | cond c role b p q hget =>
    use g
    constructor
    · exact GlobalTypeReducesStar.refl g
    · exact subject_reduction_cond g c role b p q hwt hget

  | rec c role x body hget =>
    exact subject_reduction_rec g c role x body hwt hget

/-! ## Partial Claims Bundle -/

/-- Partial claims with proven lemmas. -/
def partialClaims : SendPreservesTyping ∧ RecvPreservesTyping :=
  ⟨send_preserves_typing, recv_preserves_typing⟩

end Rumpsteak.Proofs.Safety.SubjectReduction
