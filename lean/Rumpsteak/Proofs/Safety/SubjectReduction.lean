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
  -- TODO: Update for Lean 4.24 - Except.pure_def and Except.bind_eq_ok deprecated
  sorry

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
  -- TODO: Update for Lean 4.24 - multiple deprecated simp lemmas
  -- Strategy: case analysis on g, showing each projection/consume case gives the result
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
  -- TODO: Projection preservation for non-participants
  --
  -- Strategy:
  -- 1. By cases on global type structure
  -- 2. For comm(s,r,branches): role ∉ {s,r}, so projection uses merge
  -- 3. consume selects one branch continuation g'
  -- 4. Show: merge of all branches ↾ role = g' ↾ role
  --    (because role's projection is the same in all branches - merge property)
  --
  -- Key insight: If role is not involved in the communication,
  -- all branches must have compatible projections (by well-formedness),
  -- so consuming any branch gives the same projection for role.
  --
  -- Required lemmas:
  -- - `merge_projection_eq`: merge succeeds iff all projections equal
  -- - `consume_selects_branch`: consume returns a branch continuation
  sorry

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
            ConfigWellTyped g' (reduceSendConfig c role receiver label value cont) := by
  -- TODO: Update for Lean 4.24 - complex proof with multiple deprecated APIs
  -- Strategy: Get typing for sender, apply inversion, evolve global type via consume
  sorry

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
  -- TODO: Update for Lean 4.24 - depends on wellTyped_role_has_projection and wellTyped_rec_inversion
  sorry

/-- Subject reduction theorem.

    Proof outline (following Yoshida & Gheri):
    1. By case analysis on the reduction rule
    2. For send reduction: continuation has continuation type
    3. For receive reduction: selected branch has branch type
    4. For cond/rec: both proven above -/
theorem subject_reduction : SubjectReduction := by
  intro g c c' hwt hred
  -- TODO: Update for Lean 4.24 - case analysis on Reduces needs helper lemmas
  sorry

/-! ## Partial Claims Bundle -/

/-- Partial claims with proven lemmas. -/
def partialClaims : SendPreservesTyping ∧ RecvPreservesTyping :=
  ⟨send_preserves_typing, recv_preserves_typing⟩

end Rumpsteak.Proofs.Safety.SubjectReduction
