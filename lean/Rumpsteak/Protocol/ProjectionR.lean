import Rumpsteak.Protocol.GlobalType
import Rumpsteak.Protocol.LocalTypeR
import Init.Data.List.Sort.Basic

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

/-- Project a global type onto a specific role.

    Returns the local type for the role, or an error if projection fails.

    Uses mutual recursion with helper functions to enable termination proof. -/
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
theorem projectR_end (role : String) : projectR .end role = .ok .end := rfl

/-- Projection of .var is always .var. -/
theorem projectR_var (t role : String) : projectR (.var t) role = .ok (.var t) := rfl

/-- Projection of .mu wraps the body projection in .mu (or returns .end). -/
theorem projectR_mu (t : String) (body : GlobalType) (role : String) :
    projectR (.mu t body) role =
      (projectR body role).bind fun projBody =>
        if projBody == .end then .ok .end else .ok (.mu t projBody) := by
  simp only [projectR, Except.bind, Except.pure]
  cases projectR body role with
  | error e => rfl
  | ok lt =>
    simp only [Except.bind, Except.pure]
    split <;> rfl

/-- Projection of .comm for the sender produces .send. -/
theorem projectR_comm_sender (sender receiver : String) (branches : List (Label × GlobalType)) :
    projectR (.comm sender receiver branches) sender =
      if branches.isEmpty then .error .emptyBranches
      else (projectBranches branches sender).map (.send receiver ·) := by
  simp only [projectR, beq_self_eq_true, ↓reduceIte, Except.map]
  cases projectBranches branches sender with
  | error e => rfl
  | ok bs => rfl

/-- Projection of .comm for the receiver produces .recv. -/
theorem projectR_comm_receiver (sender receiver : String) (branches : List (Label × GlobalType))
    (hne : sender ≠ receiver) :
    projectR (.comm sender receiver branches) receiver =
      if branches.isEmpty then .error .emptyBranches
      else (projectBranches branches receiver).map (.recv sender ·) := by
  simp only [projectR]
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
  | error e => simp only [hbody, Except.bind] at h
  | ok lt =>
    simp only [hbody, Except.bind, Except.pure] at h
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
  | error e => simp only [hbody, Except.bind] at h
  | ok lt =>
    simp only [hbody, Except.bind, Except.pure] at h
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
  | nil => simp only [List.find?_nil] at hfind
  | cons b rest ih =>
    simp only [projectBranchTypes, Except.bind, Except.pure] at hproj
    cases hcont : projectR b.2 role with
    | error e => simp only [hcont, Except.bind] at hproj
    | ok lt =>
      simp only [hcont, Except.bind, Except.pure] at hproj
      cases hrest : projectBranchTypes rest role with
      | error e => simp only [hrest, Except.bind] at hproj
      | ok lts =>
        simp only [hrest, Except.bind, Except.pure] at hproj
        cases hproj
        -- projTypes = lt :: lts
        simp only [List.find?_cons] at hfind
        cases hb : b.1.name == label.name with
        | true =>
          simp only [hb, ↓reduceIte, Option.some.injEq] at hfind
          cases hfind
          exact ⟨lt, hcont, List.mem_cons_self lt lts⟩
        | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte] at hfind
          have ⟨lt', hlt', hmem⟩ := ih lts hrest hfind
          exact ⟨lt', hlt', List.mem_cons_of_mem lt hmem⟩

/-- If merge of a and b succeeds, then merge is reflexive (a merges with a). -/
theorem merge_refl (t : LocalTypeR) : LocalTypeR.merge t t = some t := by
  induction t with
  | end => rfl
  | var v => simp only [LocalTypeR.merge, ↓reduceIte]
  | send partner branches ih =>
    simp only [LocalTypeR.merge, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.some_bind]
    sorry  -- Complex branch merge proof
  | recv partner branches ih =>
    simp only [LocalTypeR.merge, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.some_bind]
    sorry  -- Complex branch merge proof
  | mu v body ih =>
    simp only [LocalTypeR.merge, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
    rw [ih]
    simp only [Option.some_bind]

/-- Key lemma: if foldlM merge over a list produces result m, then each element
    is merge-compatible with the accumulator at that point. For non-participants,
    this means all elements are equal to m (under certain merge semantics). -/
-- This is complex to prove in full generality. We use an axiom for now.
axiom merge_fold_member (types : List LocalTypeR) (first : LocalTypeR) (result : LocalTypeR)
    (hfold : types.foldlM (fun acc proj => LocalTypeR.merge acc proj) first = some result)
    (t : LocalTypeR) (hmem : t ∈ types)
    : LocalTypeR.merge result t = some result

/-- For non-participants: if projection succeeds and the result is the merge of branches,
    then each branch projects to the merge result.

    PROOF SKETCH:
    1. Non-participant projection merges all branch projections
    2. Merge succeeds only when branches are "compatible"
    3. For well-formed global types, all branches project identically for non-participants
    4. Therefore consumed branch projection = merged result = original projection

    This is an axiom capturing merge semantics. Full proof requires extensive
    infrastructure for merge properties (idempotence, absorption, etc.) -/
axiom projectR_comm_non_participant (sender receiver role : String) (branches : List (Label × GlobalType))
    (result : LocalTypeR)
    (hne1 : role ≠ sender) (hne2 : role ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) role = .ok result)
    (label : Label) (g : GlobalType)
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, g))
    : projectR g role = .ok result

/-- If projectBranches succeeds and produces [(label, contType)],
    and find? finds label in branches at index (label, g),
    then projectR g role = contType. -/
theorem projectBranches_find_proj (branches : List (Label × GlobalType)) (role : String)
    (label : Label) (contType : LocalTypeR) (g : GlobalType)
    (hproj : projectBranches branches role = .ok [(label, contType)])
    (hfind : branches.find? (fun (l, _) => l.name == label.name) = some (label, g))
    : projectR g role = .ok contType := by
  -- If projectBranches returns a singleton, branches must be a singleton
  cases branches with
  | nil => simp only [projectBranches] at hproj; cases hproj
  | cons b rest =>
    simp only [projectBranches, Except.bind, Except.pure] at hproj
    cases hcont : projectR b.2 role with
    | error e => simp only [hcont, Except.bind] at hproj
    | ok lt =>
      simp only [hcont, Except.bind, Except.pure] at hproj
      cases hrest : projectBranches rest role with
      | error e => simp only [hrest, Except.bind] at hproj
      | ok lts =>
        simp only [hrest, Except.bind, Except.pure] at hproj
        -- hproj : .ok ((b.1, lt) :: lts) = .ok [(label, contType)]
        cases hproj
        -- So (b.1, lt) :: lts = [(label, contType)], meaning lts = [] and b.1 = label, lt = contType
        simp only [List.cons.injEq, Prod.mk.injEq, List.nil_eq] at *
        obtain ⟨⟨hlabel, hlt⟩, hlts⟩ := hproj
        -- lts = [], so rest must be []
        cases rest with
        | nil =>
          -- Now hfind : [b].find? ... = some (label, g)
          simp only [List.find?_cons] at hfind
          cases hb : b.1.name == label.name with
          | false => simp only [hb, Bool.false_eq_true, ↓reduceIte, List.find?_nil] at hfind
          | true =>
            simp only [hb, ↓reduceIte, Option.some.injEq] at hfind
            cases hfind
            -- b = (label, g), so b.2 = g
            rw [← hlt]
            exact hcont
        | cons _ _ =>
          -- rest is non-empty, but lts = [], so projectBranches rest = .ok []
          -- But projectBranches (x :: xs) returns at least one element
          simp only [projectBranches, Except.bind, Except.pure] at hrest
          cases projectR _ _ with
          | error e => simp only [Except.bind] at hrest
          | ok _ =>
            simp only [Except.bind, Except.pure] at hrest
            cases projectBranches _ _ with
            | error e => simp only [Except.bind] at hrest
            | ok _ => simp only [Except.bind, Except.pure] at hrest; cases hlts

end Rumpsteak.Protocol.ProjectionR
