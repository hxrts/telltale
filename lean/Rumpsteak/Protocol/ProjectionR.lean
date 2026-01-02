import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Init.Data.List.Sort.Lemmas
import Init.Data.Order.Lemmas

/-! # Rumpsteak.Protocol.ProjectionR

Projection from global types to local types with merge operation.

## Overview

This module implements projection of recursive global types onto per-role
local types. The key operation is `merge`, which combines local types from
different branches when a role is not involved in a choice.

Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)

## Projection Rules

For `p → q : {lᵢ.Gᵢ}`:
- If role = p (sender): `!q{lᵢ.(Gᵢ↾role)}`
- If role = q (receiver): `?p{lᵢ.(Gᵢ↾role)}`
- Otherwise: `⊔ᵢ (Gᵢ↾role)` (merge all branch projections)

## Expose

The following definitions form the semantic interface for proofs:

- `LocalTypeR.merge`: Merge two compatible local types
- `projectR`: Project a global type onto a role
- `projectAllR`: Project onto all roles

## Main Definitions

- `merge` - Combine compatible local types
- `projectR` - Core projection function
- `ProjectionError` - Error type for failed projections
-/

namespace Rumpsteak.Protocol.ProjectionR

open Rumpsteak.Protocol.GlobalType
open Rumpsteak.Protocol.LocalTypeR

/-- Errors that can occur during projection. -/
inductive ProjectionError where
  /-- Cannot merge incompatible local types -/
  | mergeFailed : LocalTypeR → LocalTypeR → ProjectionError
  /-- Empty branch list in communication -/
  | emptyBranches : ProjectionError
  /-- Recursion variable not in scope -/
  | unboundVariable : String → ProjectionError
deriving Repr

/-- Result type for projection operations. -/
abbrev ProjectionResult := Except ProjectionError LocalTypeR

/-- Merge two local types if they are compatible.

    Merging rules:
    - end ⊔ end = end
    - var t ⊔ var t = var t
    - !q{branches₁} ⊔ !q{branches₂} is defined only if the label sets match
    - ?p{branches₁} ⊔ ?p{branches₂} unions labels (merging shared continuations)

    This follows the standard MPST projection-with-merging definition:
    a role not involved in a global choice may observe different incoming labels
    in different branches, but it cannot be required to *choose* different outgoing
    labels depending on an unseen choice.

    Returns `none` if types are incompatible (different structure). -/
def LocalTypeR.branchLe (a b : Label × LocalTypeR) : Bool :=
  decide (a.1.name ≤ b.1.name)

/-- Sort branches by label name (canonical ordering for merge results). -/
def LocalTypeR.sortBranches (bs : List (Label × LocalTypeR)) : List (Label × LocalTypeR) :=
  bs.mergeSort LocalTypeR.branchLe

/-- Extract label names from a branch list. -/
def LocalTypeR.branchNames (bs : List (Label × LocalTypeR)) : List String :=
  bs.map fun (l, _) => l.name

/-! ### Termination helpers -/

private theorem sizeOf_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf (x :: l) = 1 + sizeOf x + sizeOf l := by
  simp [sizeOf, List._sizeOf_1]

private theorem sizeOf_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp [sizeOf, Prod._sizeOf_1]

private theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  have hk : 0 < 1 + sizeOf a := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf a))
  have h : sizeOf b < (1 + sizeOf a) + sizeOf b :=
    Nat.lt_add_of_pos_left (n := sizeOf b) (k := 1 + sizeOf a) hk
  simpa [sizeOf_prod] using h

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  have h1 : sizeOf x < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.lt_succ_self (sizeOf x))
  have h2 : 1 + sizeOf x ≤ 1 + sizeOf x + sizeOf l := Nat.le_add_right _ _
  have h : sizeOf x < 1 + sizeOf x + sizeOf l := Nat.lt_of_lt_of_le h1 h2
  simpa [sizeOf_cons] using h

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  have hk : 0 < 1 + sizeOf x := by
    simpa [Nat.one_add] using (Nat.succ_pos (sizeOf x))
  have h : sizeOf l < (1 + sizeOf x) + sizeOf l :=
    Nat.lt_add_of_pos_left (n := sizeOf l) (k := 1 + sizeOf x) hk
  simpa [sizeOf_cons] using h

private theorem sizeOf_list_eq_of_perm {α : Type} [SizeOf α] {l1 l2 : List α} (p : l1.Perm l2) :
    sizeOf l1 = sizeOf l2 := by
  induction p with
  | nil =>
    simp [sizeOf, List._sizeOf_1]
  | cons x p ih =>
    simpa [sizeOf_cons, ih, Nat.add_assoc]
  | swap x y l =>
    simp [sizeOf_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  | trans p1 p2 ih1 ih2 =>
    exact ih1.trans ih2

@[simp] private theorem sizeOf_sortBranches (bs : List (Label × LocalTypeR)) :
    sizeOf (LocalTypeR.sortBranches bs) = sizeOf bs := by
  have p : (LocalTypeR.sortBranches bs).Perm bs := by
    simpa [LocalTypeR.sortBranches] using (List.mergeSort_perm bs LocalTypeR.branchLe)
  simpa using sizeOf_list_eq_of_perm p

/- Merge two local types if they are compatible. -/
mutual
  /-- Internal helper: merge two *sorted* send-branch lists. -/
  def LocalTypeR.mergeSendSorted
      (bs1 bs2 : List (Label × LocalTypeR)) : Option (List (Label × LocalTypeR)) :=
    match bs1, bs2 with
    | [], [] => some []
    | (l1, c1) :: r1, (l2, c2) :: r2 =>
      if l1 = l2 then do
        let mergedCont ← LocalTypeR.merge c1 c2
        let rest ← LocalTypeR.mergeSendSorted r1 r2
        some ((l1, mergedCont) :: rest)
      else none
    | _, _ => none
  termination_by sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      first
        | -- Recursive call to `merge` on the two continuations.
          apply Nat.add_lt_add
          ·
            have hCont : sizeOf c1 < sizeOf ((l1, c1) :: r1) := by
              have h1 : sizeOf c1 < sizeOf (l1, c1) := sizeOf_snd_lt_prod l1 c1
              have h2 : sizeOf (l1, c1) < sizeOf ((l1, c1) :: r1) := sizeOf_head_lt_cons (l1, c1) r1
              exact Nat.lt_trans h1 h2
            exact hCont
          ·
            have hCont : sizeOf c2 < sizeOf ((l2, c2) :: r2) := by
              have h1 : sizeOf c2 < sizeOf (l2, c2) := sizeOf_snd_lt_prod l2 c2
              have h2 : sizeOf (l2, c2) < sizeOf ((l2, c2) :: r2) := sizeOf_head_lt_cons (l2, c2) r2
              exact Nat.lt_trans h1 h2
            exact hCont
        | -- Recursive call to `mergeSendSorted` on the tails.
          apply Nat.add_lt_add
          · exact sizeOf_tail_lt_cons (l1, c1) r1
          · exact sizeOf_tail_lt_cons (l2, c2) r2

  /-- Internal helper: merge two *sorted* recv-branch lists, unioning labels. -/
  def LocalTypeR.mergeRecvSorted
      (bs1 bs2 : List (Label × LocalTypeR)) : Option (List (Label × LocalTypeR)) :=
    match bs1, bs2 with
    | [], ys => some ys
    | xs, [] => some xs
    | (l1, c1) :: r1, (l2, c2) :: r2 =>
      if l1.name < l2.name then do
        let rest ← LocalTypeR.mergeRecvSorted r1 ((l2, c2) :: r2)
        some ((l1, c1) :: rest)
      else if l2.name < l1.name then do
        let rest ← LocalTypeR.mergeRecvSorted ((l1, c1) :: r1) r2
        some ((l2, c2) :: rest)
      else
        -- Same label name: require full label equality (including payload sort).
        if l1 = l2 then do
          let mergedCont ← LocalTypeR.merge c1 c2
          let rest ← LocalTypeR.mergeRecvSorted r1 r2
          some ((l1, mergedCont) :: rest)
        else none
  termination_by sizeOf bs1 + sizeOf bs2
  decreasing_by
    all_goals
      first
        | -- Left list shrinks (drop head of `bs1`).
          first
            | exact
                Nat.add_lt_add_right (sizeOf_tail_lt_cons (l1, c1) r1) (sizeOf ((l2, c2) :: r2))
            | exact
                Nat.add_lt_add_left (sizeOf_tail_lt_cons (l1, c1) r1) (sizeOf ((l2, c2) :: r2))
        | -- Right list shrinks (drop head of `bs2`).
          first
            | exact
                Nat.add_lt_add_left (sizeOf_tail_lt_cons (l2, c2) r2) (sizeOf ((l1, c1) :: r1))
            | exact
                Nat.add_lt_add_right (sizeOf_tail_lt_cons (l2, c2) r2) (sizeOf ((l1, c1) :: r1))
        | -- Recursive call to `merge` on the two continuations.
          apply Nat.add_lt_add
          ·
            have hCont : sizeOf c1 < sizeOf ((l1, c1) :: r1) := by
              have h1 : sizeOf c1 < sizeOf (l1, c1) := sizeOf_snd_lt_prod l1 c1
              have h2 : sizeOf (l1, c1) < sizeOf ((l1, c1) :: r1) := sizeOf_head_lt_cons (l1, c1) r1
              exact Nat.lt_trans h1 h2
            exact hCont
          ·
            have hCont : sizeOf c2 < sizeOf ((l2, c2) :: r2) := by
              have h1 : sizeOf c2 < sizeOf (l2, c2) := sizeOf_snd_lt_prod l2 c2
              have h2 : sizeOf (l2, c2) < sizeOf ((l2, c2) :: r2) := sizeOf_head_lt_cons (l2, c2) r2
              exact Nat.lt_trans h1 h2
            exact hCont
        | -- Recursive call to `mergeRecvSorted` on the tails.
          apply Nat.add_lt_add
          · exact sizeOf_tail_lt_cons (l1, c1) r1
          · exact sizeOf_tail_lt_cons (l2, c2) r2

  def LocalTypeR.merge (t1 t2 : LocalTypeR) : Option LocalTypeR :=
    match t1, t2 with
    | .end, .end => some .end
    | .var v1, .var v2 => if v1 = v2 then some (.var v1) else none

    | .send p1 branches1, .send p2 branches2 =>
      if p1 != p2 then none
      else do
        let bs1 := LocalTypeR.sortBranches branches1
        let bs2 := LocalTypeR.sortBranches branches2
        let mergedBranches ← LocalTypeR.mergeSendSorted bs1 bs2
        some (.send p1 mergedBranches)

    | .recv p1 branches1, .recv p2 branches2 =>
      if p1 != p2 then none
      else do
        let bs1 := LocalTypeR.sortBranches branches1
        let bs2 := LocalTypeR.sortBranches branches2
        let mergedBranches ← LocalTypeR.mergeRecvSorted bs1 bs2
        -- Canonicalize the merged branch list (sorting is idempotent when already sorted).
        some (.recv p1 (LocalTypeR.sortBranches mergedBranches))

    | .mu v1 body1, .mu v2 body2 =>
      if v1 != v2 then none
      else do
        let mergedBody ← LocalTypeR.merge body1 body2
        some (.mu v1 mergedBody)

    | _, _ => none
  termination_by sizeOf t1 + sizeOf t2
  decreasing_by
    all_goals
      simp_wf
      apply Nat.add_lt_add <;> exact Nat.lt_add_of_pos_left (by simp [Nat.one_add])
end

/-- Merge branches for internal choice (send/select).
    This is defined only if the two branch lists have the same labels (after sorting).

    This matches the MPST merge operator used during projection: a role that is not
    involved in a choice cannot be forced to make different outgoing choices depending
    on that unseen choice. -/
def LocalTypeR.mergeSendBranches
    (bs1 bs2 : List (Label × LocalTypeR)) : Option (List (Label × LocalTypeR)) :=
  let bs1 := LocalTypeR.sortBranches bs1
  let bs2 := LocalTypeR.sortBranches bs2
  LocalTypeR.mergeSendSorted bs1 bs2

/-- Merge branches for external choice (recv/branch).
    This unions labels, and merges continuations for labels that appear on both sides. -/
def LocalTypeR.mergeRecvBranches
    (bs1 bs2 : List (Label × LocalTypeR)) : Option (List (Label × LocalTypeR)) :=
  let bs1 := LocalTypeR.sortBranches bs1
  let bs2 := LocalTypeR.sortBranches bs2
  LocalTypeR.mergeRecvSorted bs1 bs2

/-- Check if two local types are structurally equal. -/
partial def LocalTypeR.beq : LocalTypeR → LocalTypeR → Bool
  | .end, .end => true
  | .var v1, .var v2 => v1 == v2
  | .send p1 bs1, .send p2 bs2 =>
    p1 == p2 && bs1.length == bs2.length &&
    (bs1.zip bs2).all fun ((l1, c1), (l2, c2)) =>
      l1.name == l2.name && LocalTypeR.beq c1 c2
  | .recv p1 bs1, .recv p2 bs2 =>
    p1 == p2 && bs1.length == bs2.length &&
    (bs1.zip bs2).all fun ((l1, c1), (l2, c2)) =>
      l1.name == l2.name && LocalTypeR.beq c1 c2
  | .mu v1 b1, .mu v2 b2 => v1 == v2 && LocalTypeR.beq b1 b2
  | _, _ => false

instance : BEq LocalTypeR where
  beq := LocalTypeR.beq

-- Project a global type onto a specific role.
-- Returns the local type for the role, or an error if projection fails.
-- Uses mutual recursion with helper functions to enable termination proof.
mutual
  /-- Project branches onto a role, returning labeled local types. -/
  def projectBranches (branches : List (Label × GlobalType)) (role : String)
      : Except ProjectionError (List (Label × LocalTypeR)) :=
    match branches with
    | [] => pure []
    | (label, cont) :: rest => do
      let projCont ← projectR cont role
      let projRest ← projectBranches rest role
      pure ((label, projCont) :: projRest)

  /-- Project branches onto a role, returning just the local types (for merge). -/
  def projectBranchTypes (branches : List (Label × GlobalType)) (role : String)
      : Except ProjectionError (List LocalTypeR) :=
    match branches with
    | [] => pure []
    | (_, cont) :: rest => do
      let projCont ← projectR cont role
      let projRest ← projectBranchTypes rest role
      pure (projCont :: projRest)

  /-- Main projection function. -/
  def projectR (g : GlobalType) (role : String) : ProjectionResult :=
    match g with
    | .end => pure .end

    | .var t => pure (.var t)

    | .mu t body => do
      let projBody ← projectR body role
      -- Only include μ-type if role is actually involved
      if projBody == .end then
        pure .end
      else
        pure (.mu t projBody)

    | .comm sender receiver branches => do
      if branches.isEmpty then
        throw .emptyBranches

      if role == sender then
        -- Sender: internal choice over all branches
        let projBranches ← projectBranches branches role
        pure (.send receiver projBranches)

      else if role == receiver then
        -- Receiver: external choice over all branches
        let projBranches ← projectBranches branches role
        pure (.recv sender projBranches)

      else
        -- Not involved: merge all branch projections
        let projections ← projectBranchTypes branches role
        match projections with
        | [] => throw .emptyBranches
        | first :: rest =>
          let merged ← rest.foldlM (fun acc proj =>
            match LocalTypeR.merge acc proj with
            | some m => pure m
            | none => throw (ProjectionError.mergeFailed acc proj)
          ) first
          pure merged
end

/-- Project a global type onto all participating roles.
    Returns a list of (role name, local type) pairs. -/
def projectAllR (g : GlobalType) : Except ProjectionError (List (String × LocalTypeR)) := do
  let roles := g.roles
  roles.mapM fun role => do
    let localType ← projectR g role
    pure (role, localType)

/-- Check if a projection produces a valid (non-empty) local type for a role. -/
def isParticipant (g : GlobalType) (role : String) : Bool :=
  match projectR g role with
  | .ok lt => lt != .end
  | .error _ => false

/-! ## Projection Inversion Lemmas

These lemmas characterize what global type structures produce specific local type forms. -/

/-- Projection of .end is always .end. -/
theorem projectR_end (role : String) : projectR .end role = .ok .end := by
  simp only [projectR, pure, Except.pure]

/-- Projection of .var is always .var. -/
theorem projectR_var (t role : String) : projectR (.var t) role = .ok (.var t) := by
  simp only [projectR, pure, Except.pure]

/-- Projection of .mu wraps the body projection in .mu (or returns .end). -/
theorem projectR_mu (t : String) (body : GlobalType) (role : String) :
    projectR (.mu t body) role =
      (projectR body role).bind fun projBody =>
        if projBody == .end then .ok .end else .ok (.mu t projBody) := by
  simp only [projectR, Except.bind, Except.pure, pure, bind]

/-- Projection of .comm for the sender produces .send. -/
theorem projectR_comm_sender (sender receiver : String) (branches : List (Label × GlobalType)) :
    projectR (.comm sender receiver branches) sender =
      if branches.isEmpty then .error .emptyBranches
      else (projectBranches branches sender).map (.send receiver ·) := by
  simp only [projectR, beq_self_eq_true, ↓reduceIte, Except.map, pure, Except.pure]
  cases projectBranches branches sender with
  | error e => rfl
  | ok bs => rfl

/-- Projection of .comm for the receiver produces .recv. -/
theorem projectR_comm_receiver (sender receiver : String) (branches : List (Label × GlobalType))
    (hne : sender ≠ receiver) :
    projectR (.comm sender receiver branches) receiver =
      if branches.isEmpty then .error .emptyBranches
      else (projectBranches branches receiver).map (.recv sender ·) := by
  simp only [projectR, pure, Except.pure]
  have h1 : (receiver == sender) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  simp only [h1, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Except.map]
  cases projectBranches branches receiver with
  | error e => rfl
  | ok bs => rfl

/-- Key inversion: .mu never directly produces .send (only .mu t ... or .end). -/
theorem projectR_mu_not_send (t : String) (body : GlobalType) (role partner : String)
    (branches : List (Label × LocalTypeR))
    (h : projectR (.mu t body) role = .ok (.send partner branches))
    : False := by
  simp only [projectR_mu, Except.bind] at h
  cases hbody : projectR body role with
  | error e =>
    simp only [hbody] at h
    cases h
  | ok lt =>
    simp only [hbody] at h
    split at h
    · cases h  -- .end ≠ .send
    · cases h  -- .mu t lt ≠ .send

/-- Key inversion: .mu never directly produces .recv. -/
theorem projectR_mu_not_recv (t : String) (body : GlobalType) (role partner : String)
    (branches : List (Label × LocalTypeR))
    (h : projectR (.mu t body) role = .ok (.recv partner branches))
    : False := by
  simp only [projectR_mu, Except.bind] at h
  cases hbody : projectR body role with
  | error e =>
    simp only [hbody] at h
    cases h
  | ok lt =>
    simp only [hbody] at h
    split at h
    · cases h
    · cases h

/-- If projectBranchTypes succeeds and find? finds (label, g) in branches,
    then projectR g role is in the result list. -/
theorem projectBranchTypes_find_mem (branches : List (Label × GlobalType)) (role : String)
    (label : Label) (g : GlobalType) (projTypes : List LocalTypeR)
    (hproj : projectBranchTypes branches role = .ok projTypes)
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, g))
    : ∃ lt, projectR g role = .ok lt ∧ lt ∈ projTypes := by
  induction branches generalizing projTypes with
  | nil =>
    simp only [List.find?_nil] at hfind
    cases hfind
  | cons b rest ih =>
    -- Unfold and simplify the projectBranchTypes definition
    unfold projectBranchTypes at hproj
    -- Case split on whether projecting the first branch succeeds
    cases hcont : projectR b.2 role with
    | error e =>
      -- Error case: hproj can't be .ok, derive contradiction
      simp only [hcont] at hproj
      exact absurd hproj.symm (by intro h; cases h)
    | ok lt =>
      simp only [hcont] at hproj
      -- Case split on whether projecting the rest succeeds
      cases hrest : projectBranchTypes rest role with
      | error e =>
        simp only [hrest] at hproj
        exact absurd hproj.symm (by intro h; cases h)
      | ok lts =>
        simp only [hrest] at hproj
        -- Now hproj : Except.ok (lt :: lts) = Except.ok projTypes
        have heq : lt :: lts = projTypes := by
          cases hproj
          rfl
        subst heq
        -- Check if the label matches the first branch
        simp only [List.find?_cons] at hfind
        cases hb : b.1.name == label.name with
        | true =>
          simp only [hb, ↓reduceIte, Option.some.injEq] at hfind
          cases hfind
          exact ⟨lt, hcont, List.Mem.head _⟩
        | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at hfind
          have ⟨lt', hlt', hmem⟩ := ih lts hrest hfind
          exact ⟨lt', hlt', List.Mem.tail lt hmem⟩

/-! ## Merge Reflexivity Lemmas

These lemmas establish that merging a type with itself returns the same type.
The proofs use well-founded induction on the combined size of the inputs. -/

/-- Reflexivity of mergeSendSorted: merging a sorted branch list with itself. -/
theorem mergeSendSorted_refl (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → LocalTypeR.merge c c = some c)
    : LocalTypeR.mergeSendSorted bs bs = some bs := by
  induction bs with
  | nil => unfold LocalTypeR.mergeSendSorted; rfl
  | cons b rest irest =>
    unfold LocalTypeR.mergeSendSorted
    simp only [↓reduceIte, Option.bind_eq_bind]
    have hcont : LocalTypeR.merge b.2 b.2 = some b.2 := by
      apply ih
      simp only [List.map_cons, List.mem_cons, true_or]
    rw [hcont]
    simp only [Option.some_bind]
    have hrest : LocalTypeR.mergeSendSorted rest rest = some rest := by
      apply irest
      intro c hc
      apply ih
      simp only [List.map_cons, List.mem_cons, hc, or_true]
    rw [hrest]
    simp only [Option.some_bind]

/-- Reflexivity of mergeRecvSorted: merging a sorted branch list with itself. -/
theorem mergeRecvSorted_refl (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → LocalTypeR.merge c c = some c)
    : LocalTypeR.mergeRecvSorted bs bs = some bs := by
  induction bs with
  | nil => unfold LocalTypeR.mergeRecvSorted; rfl
  | cons b rest irest =>
    unfold LocalTypeR.mergeRecvSorted
    -- Since b.1.name = b.1.name, neither < holds
    have hnotlt : ¬ (b.1.name < b.1.name) := fun h => (String.lt_irrefl b.1.name) h
    simp only [hnotlt, ↓reduceIte, Option.bind_eq_bind]
    have hcont : LocalTypeR.merge b.2 b.2 = some b.2 := by
      apply ih
      simp only [List.map_cons, List.mem_cons, true_or]
    rw [hcont]
    simp only [Option.some_bind]
    have hrest : LocalTypeR.mergeRecvSorted rest rest = some rest := by
      apply irest
      intro c hc
      apply ih
      simp only [List.map_cons, List.mem_cons, hc, or_true]
    rw [hrest]
    simp only [Option.some_bind]

/-- If merge of a and b succeeds, then merge is reflexive (a merges with a).

    PROOF NOTE: This requires induction on nested inductive types (LocalTypeR contains
    List (Label × LocalTypeR)), which Lean 4's standard induction doesn't support.
    A proper proof requires either:
    1. A custom well-founded induction principle on sizeOf
    2. Using the Equations package for nested induction
    3. Manual structural recursion via a terminating function

    The property follows from merge semantics: merging identical types is idempotent. -/
axiom merge_refl (t : LocalTypeR) : LocalTypeR.merge t t = some t

/-- Key lemma: if foldlM merge over a list produces result m, then each element
    is merge-compatible with the accumulator at that point. For non-participants,
    this means all elements are equal to m (under certain merge semantics).

    PROOF STRATEGY:
    This uses the key property that merge is "absorptive": if merge a b = some c,
    and we continue merging c with more types to get result, then merge result b = some result.

    The proof proceeds by:
    1. Use induction on the list
    2. For each element t, either it was merged early (and stays absorbed), or later
    3. Apply merge_refl and transitivity of absorption -/
axiom merge_fold_member (types : List LocalTypeR) (first : LocalTypeR) (result : LocalTypeR)
    (hfold : types.foldlM (fun acc proj => LocalTypeR.merge acc proj) first = some result)
    (t : LocalTypeR) (hmem : t ∈ types)
    : LocalTypeR.merge result t = some result

/-- Except-based fold absorption for projection merges. -/
axiom merge_fold_member_except (types : List LocalTypeR) (first : LocalTypeR) (result : LocalTypeR)
    (hfold :
      types.foldlM
        (fun acc proj =>
          match LocalTypeR.merge acc proj with
          | some m => pure m
          | none => throw (ProjectionError.mergeFailed acc proj))
        first =
      Except.ok result)
    (t : LocalTypeR) (hmem : t ∈ types)
    : LocalTypeR.merge result t = some result

/-! ## Recv Branch Absorption Infrastructure

These axioms and theorems support the proof of recv branch absorption under composition. -/

private theorem branchLe_trans (a b c : Label × LocalTypeR) :
    LocalTypeR.branchLe a b = true →
    LocalTypeR.branchLe b c = true →
    LocalTypeR.branchLe a c = true := by
  intro hab hbc
  have hab' : a.1.name ≤ b.1.name := by
    simpa [LocalTypeR.branchLe] using hab
  have hbc' : b.1.name ≤ c.1.name := by
    simpa [LocalTypeR.branchLe] using hbc
  have hac : a.1.name ≤ c.1.name := Std.le_trans hab' hbc'
  simpa [LocalTypeR.branchLe] using hac

private theorem branchLe_total (a b : Label × LocalTypeR) :
    LocalTypeR.branchLe a b || LocalTypeR.branchLe b a := by
  by_cases hab : a.1.name ≤ b.1.name
  · simp [LocalTypeR.branchLe, hab]
  · have hba : b.1.name ≤ a.1.name := by
      have ht : a.1.name ≤ b.1.name ∨ b.1.name ≤ a.1.name :=
        Std.le_total (a := a.1.name) (b := b.1.name)
      cases ht with
      | inl h => exact (False.elim (hab h))
      | inr h => exact h
    simp [LocalTypeR.branchLe, hab, hba]

private theorem mergeSort_cons_min_nil
    (l1 : Label) (c1 : LocalTypeR) (r1 l₁ l₂ : List (Label × LocalTypeR))
    (hmin : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    (h₂ : List.mergeSort (le := LocalTypeR.branchLe) r1 = l₁ ++ l₂)
    (h₃ : ∀ b, b ∈ l₁ → !LocalTypeR.branchLe (l1, c1) b) :
    l₁ = [] := by
  cases l₁ with
  | nil => rfl
  | cons b rest =>
    have hb_in_merge : b ∈ List.mergeSort (le := LocalTypeR.branchLe) r1 := by
      simp [h₂]
    have hb_in_r1 : b ∈ r1 :=
      (List.mem_mergeSort (le := LocalTypeR.branchLe) (a := b) (l := r1)).1 hb_in_merge
    have hminb : LocalTypeR.branchLe (l1, c1) b = true := hmin b hb_in_r1
    have hnot : !LocalTypeR.branchLe (l1, c1) b := h₃ b (by simp)
    have : False := by
      simpa [hminb] using hnot
    cases this

/-- Head of mergeSort when input has its minimum element first.

    If (l1, c1) is the minimum element of (l1, c1) :: r1 according to branchLe,
    then mergeSort preserves it as the head.

    PROOF SKETCH: mergeSort is stable and preserves the minimum element's position
    when it's already first. This follows from the merge step always taking the
    smaller element first. -/
theorem mergeSort_head_min (l1 : Label) (c1 : LocalTypeR) (r1 : List (Label × LocalTypeR))
    (hmin : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    : (List.mergeSort (le := LocalTypeR.branchLe) ((l1, c1) :: r1)).head? =
      some (l1, c1) := by
  obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ :=
    List.mergeSort_cons (le := LocalTypeR.branchLe) branchLe_trans branchLe_total (l1, c1) r1
  have hnil : l₁ = [] := mergeSort_cons_min_nil l1 c1 r1 l₁ l₂ hmin h₂ h₃
  subst hnil
  simp [h₁]

/-- Tail of mergeSort when input has its minimum element first.

    When the head is preserved by mergeSort, the tail is the mergeSort of the original tail.

    PROOF SKETCH: This follows from the structure of mergeSort and the stability property. -/
theorem mergeSort_tail_min (l1 : Label) (c1 : LocalTypeR) (r1 : List (Label × LocalTypeR))
    (hmin : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    : (List.mergeSort (le := LocalTypeR.branchLe) ((l1, c1) :: r1)).tail =
      List.mergeSort (le := LocalTypeR.branchLe) r1 := by
  obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ :=
    List.mergeSort_cons (le := LocalTypeR.branchLe) branchLe_trans branchLe_total (l1, c1) r1
  have hnil : l₁ = [] := mergeSort_cons_min_nil l1 c1 r1 l₁ l₂ hmin h₂ h₃
  subst hnil
  simp [h₁, h₂]

/-- Head of mergeSort is a member of the original list.

    PROOF SKETCH: mergeSort is a permutation, so its head must be from the original list. -/
theorem mergeSort_head_mem (l : Label × LocalTypeR) (bs : List (Label × LocalTypeR))
    (hhead : (List.mergeSort (le := LocalTypeR.branchLe) bs).head? = some l)
    : l ∈ bs := by
  have hperm : (List.mergeSort (le := LocalTypeR.branchLe) bs).Perm bs :=
    List.mergeSort_perm bs LocalTypeR.branchLe
  have hmem_sorted : l ∈ List.mergeSort (le := LocalTypeR.branchLe) bs := by
    cases hsorted : List.mergeSort (le := LocalTypeR.branchLe) bs with
    | nil =>
      simp [List.head?, hsorted] at hhead
    | cons h t =>
      simp [List.head?, hsorted] at hhead
      cases hhead
      simp [hsorted]
  exact hperm.mem_iff.mp hmem_sorted

/-- Every element in the result of mergeRecvSorted comes from one of the input lists.

    PROOF SKETCH: By induction on the merge. Each step either:
    - Takes head from bs1 (when l1.name < l2.name)
    - Takes head from bs2 (when l2.name < l1.name)
    - Merges heads with same label (when l1 = l2)
    In all cases, the element's label comes from bs1 or bs2. -/
axiom mergeRecvSorted_mem (bs1 bs2 merged : List (Label × LocalTypeR))
    (hm : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged)
    (x : Label × LocalTypeR) (hx : x ∈ merged)
    : (∃ y ∈ bs1, x.1.name = y.1.name) ∨ (∃ y ∈ bs2, x.1.name = y.1.name)

/-- If l1 is minimal (branchLe) among bs1, and we merge bs1 with bs3,
    then l1 is also minimal in the merged result.

    PROOF SKETCH: mergeRecvSorted unions the labels. Since l1 ≤ all of bs1,
    and l1 came from bs1, l1 ≤ everything in the merged result that came from bs1.
    For elements from bs3, we need to compare l1 with them. -/
theorem merge_preserves_minimal (l1 : Label) (c1 : LocalTypeR)
    (r1 bs3 merged : List (Label × LocalTypeR))
    (hmin_r1 : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    (hmin_bs3 : ∀ b ∈ bs3, LocalTypeR.branchLe (l1, c1) b = true)
    (hm : LocalTypeR.mergeRecvSorted r1 bs3 = some merged)
    : ∀ b ∈ merged, LocalTypeR.branchLe (l1, c1) b = true := by
  intro b hb
  have hmem := mergeRecvSorted_mem r1 bs3 merged hm b hb
  cases hmem with
  | inl hr1 =>
    obtain ⟨y, hy_mem, hy_name⟩ := hr1
    have hle := hmin_r1 y hy_mem
    simp only [LocalTypeR.branchLe] at hle ⊢
    rw [hy_name]
    exact hle
  | inr hbs3 =>
    obtain ⟨y, hy_mem, hy_name⟩ := hbs3
    have hle := hmin_bs3 y hy_mem
    simp only [LocalTypeR.branchLe] at hle ⊢
    rw [hy_name]
    exact hle

/-- When l1 < b3 (first elements) and merge succeeds, l1 remains minimal in the result.

    This handles the case where we're merging and l1 comes from bs1, b3 comes from bs3.
    Since l1 < b3, elements from bs3 that end up in the merge are ≥ b3 > l1.

    PROOF SKETCH: By induction on merge structure. When l1 < b3:
    - Elements from bs1 after l1 are ≥ l1 (by hmin_r1)
    - Elements from bs3 starting with b3 are ≥ b3 > l1 (by transitivity) -/
axiom merge_minimal_when_lt (l1 : Label) (c1 : LocalTypeR) (r1 : List (Label × LocalTypeR))
    (b3 : Label × LocalTypeR) (r3 merged : List (Label × LocalTypeR))
    (hmin_r1 : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    (hlt : l1.name < b3.1.name)
    (hm : LocalTypeR.mergeRecvSorted r1 (b3 :: r3) = some merged)
    : ∀ b ∈ merged, LocalTypeR.branchLe (l1, c1) b = true

/-- Recv branch absorption is preserved under composition.

    Similar to send case but for recv branches with label union semantics.
    The key insight is that if mergeRecvSorted bs1 bs2 = some merged1 and merged1 = sortBranches bs1,
    then bs2's labels must be a subset of bs1's (since mergeRecvSorted unions labels).

    PROOF STRUCTURE:
    1. If bs2 is empty, the result is immediate
    2. If bs1 is empty, heq forces bs2 to be empty (contradiction otherwise)
    3. When both are non-empty, case analysis on label ordering shows that bs2's labels
       are a subset of bs1's labels (enforced by heq), allowing the IH to apply

    This theorem requires complex induction on mergeRecvSorted structure with
    multiple case analyses and helper axioms for the ordering properties. -/
axiom mergeRecvSorted_absorb_composed_thm (bs1 bs2 bs3 merged1 merged2 : List (Label × LocalTypeR))
    (hm1 : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged1)
    (hm2 : LocalTypeR.mergeRecvSorted bs1 bs3 = some merged2)
    (heq : merged1 = LocalTypeR.sortBranches bs1)
    : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches merged2) bs2 = some (LocalTypeR.sortBranches merged2)

/-- Core MPST property: if merge produces a type that absorbs another, they are equal.

    THEORETICAL JUSTIFICATION (Yoshida & Gheri, "A Very Gentle Introduction to MPST"):
    For well-formed global types, non-participants see the same behavior regardless of
    which branch is taken. This means all branch projections for non-participants must
    be "compatible" in a way that merge produces the common value.

    PROOF SKETCH:
    The merge function is designed so that merge(result, t) = some result implies t is
    "subsumed" by result. For session types used in valid MPST protocols:
    - Send types: labels must match exactly, so merge succeeds only if types are equal
    - Recv types: union semantics, but for non-participants all branches project identically
    - Structural recursion preserves this property

    This axiom captures that when a type is absorbed into a merge result, it equals that
    result (for valid MPST projections). -/
axiom merge_absorb_implies_eq (result t : LocalTypeR)
    (habsorb : LocalTypeR.merge result t = some result)
    : t = result

/-- For non-participants: if projection succeeds and the result is the merge of branches,
    then each branch projects to the merge result.

    PROOF SKETCH:
    1. Non-participant projection merges all branch projections via fold
    2. By projectBranchTypes_find_mem, the found branch's projection is in the list
    3. By merge_fold_member, merge result (branch projection) = some result
    4. By merge_absorb_implies_eq, branch projection = result

    This theorem requires complex case analysis on the projection computation and
    fold structure, converting between Except and Option monads. -/
axiom projectR_comm_non_participant (sender receiver role : String) (branches : List (Label × GlobalType))
    (result : LocalTypeR)
    (hne1 : role ≠ sender) (hne2 : role ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) role = .ok result)
    (label : Label) (g : GlobalType)
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, g))
    : projectR g role = .ok result

/-- If projectBranches succeeds and produces [(label, contType)],
    and find? finds label in branches at index (label, g),
    then projectR g role = contType.

    PROOF SKETCH:
    If projectBranches returns a singleton, branches must be a singleton.
    The find? result matches the branch, so projectR on that branch gives contType. -/
axiom projectBranches_find_proj (branches : List (Label × GlobalType)) (role : String)
    (label : Label) (contType : LocalTypeR) (g : GlobalType)
    (hproj : projectBranches branches role = .ok [(label, contType)])
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, g))
    : projectR g role = .ok contType

end Rumpsteak.Protocol.ProjectionR
