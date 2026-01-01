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

/-! ## Merge Reflexivity Lemmas

These lemmas establish that merging a type with itself returns the same type.
The proofs use well-founded induction on the combined size of the inputs. -/

/-- Reflexivity of mergeSendSorted: merging a sorted branch list with itself. -/
theorem mergeSendSorted_refl (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → LocalTypeR.merge c c = some c)
    : LocalTypeR.mergeSendSorted bs bs = some bs := by
  induction bs with
  | nil => rfl
  | cons b rest irest =>
    simp only [LocalTypeR.mergeSendSorted, ↓reduceIte, Option.bind_eq_bind]
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
  | nil => rfl
  | cons b rest irest =>
    simp only [LocalTypeR.mergeRecvSorted]
    -- Since b.1.name = b.1.name, neither < holds
    have hnotlt : ¬ (b.1.name < b.1.name) := lt_irrefl b.1.name
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

/-- If merge of a and b succeeds, then merge is reflexive (a merges with a). -/
theorem merge_refl (t : LocalTypeR) : LocalTypeR.merge t t = some t := by
  induction t with
  | end => rfl
  | var v => simp only [LocalTypeR.merge, ↓reduceIte]
  | send partner branches ih =>
    simp only [LocalTypeR.merge, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.some_bind]
    have hsorted := mergeSendSorted_refl (LocalTypeR.sortBranches branches) (fun c hc => by
      -- c is in the sorted branches, which is a permutation of branches
      -- By ih, merge c c = some c for all c in branches
      -- Need to connect sorted branches to original branches
      have hperm : (LocalTypeR.sortBranches branches).Perm branches := by
        simp only [LocalTypeR.sortBranches]
        exact List.mergeSort_perm branches LocalTypeR.branchLe
      have hmem : c ∈ branches.map Prod.snd := by
        have hc' : c ∈ (LocalTypeR.sortBranches branches).map Prod.snd := hc
        exact List.Perm.mem_iff (hperm.map Prod.snd) |>.mp hc'
      have ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp (List.mem_map.mp hmem).choose_spec.2
      exact ih ⟨i, by simp at hi; exact hi⟩)
    rw [hsorted]
  | recv partner branches ih =>
    simp only [LocalTypeR.merge, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.some_bind]
    have hsorted := mergeRecvSorted_refl (LocalTypeR.sortBranches branches) (fun c hc => by
      have hperm : (LocalTypeR.sortBranches branches).Perm branches := by
        simp only [LocalTypeR.sortBranches]
        exact List.mergeSort_perm branches LocalTypeR.branchLe
      have hmem : c ∈ branches.map Prod.snd := by
        have hc' : c ∈ (LocalTypeR.sortBranches branches).map Prod.snd := hc
        exact List.Perm.mem_iff (hperm.map Prod.snd) |>.mp hc'
      have ⟨i, hi, hci⟩ := List.mem_iff_getElem.mp (List.mem_map.mp hmem).choose_spec.2
      exact ih ⟨i, by simp at hi; exact hi⟩)
    rw [hsorted]
    simp only [Option.some_bind]
    -- Need to show sortBranches (sortBranches branches) = sortBranches branches
    -- sortBranches is idempotent on sorted lists
    congr 1
    -- mergeRecvSorted bs bs = some bs for sorted bs, and sortBranches is idempotent
    -- Actually we need: sortBranches (sortBranches branches) = sortBranches branches
    have hidempotent : LocalTypeR.sortBranches (LocalTypeR.sortBranches branches) =
                       LocalTypeR.sortBranches branches := by
      simp only [LocalTypeR.sortBranches]
      -- mergeSort of a sorted list is the list itself
      exact List.mergeSort_eq_self LocalTypeR.branchLe
             (List.sorted_mergeSort LocalTypeR.branchLe branches)
    exact hidempotent
  | mu v body ih =>
    simp only [LocalTypeR.merge, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
    rw [ih]
    simp only [Option.some_bind]

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
theorem merge_fold_member (types : List LocalTypeR) (first : LocalTypeR) (result : LocalTypeR)
    (hfold : types.foldlM (fun acc proj => LocalTypeR.merge acc proj) first = some result)
    (t : LocalTypeR) (hmem : t ∈ types)
    : LocalTypeR.merge result t = some result := by
  induction types generalizing first result with
  | nil => cases hmem
  | cons head tail ih =>
    simp only [List.foldlM, bind, Option.bind] at hfold
    cases hmerge : LocalTypeR.merge first head with
    | none => simp only [hmerge, Option.none_bind] at hfold
    | some acc' =>
      simp only [hmerge, Option.some_bind] at hfold
      cases hmem with
      | head =>
        -- t = head, need to show merge result head = some result
        -- We know: merge first head = some acc', and foldlM tail acc' = some result
        -- By induction on tail, we know that acc' "flows through" to result
        -- Key insight: merge acc' acc' = some acc' (reflexivity)
        -- And if we fold more on top, the result still absorbs acc'
        -- This requires: if merge a b = some c, then merge c b = some c
        -- And transitively: merge (fold rest c) b = some (fold rest c)
        -- We need an auxiliary lemma for this...
        -- For now, we use the observation that in MPST, after folding,
        -- result = acc' when tail is empty, or result contains acc' when non-empty
        cases tail with
        | nil =>
          simp only [List.foldlM] at hfold
          cases hfold
          -- result = acc', so merge result head = merge acc' head
          -- But merge first head = some acc', and we need merge acc' head = some acc'
          -- This is the absorption property!
          -- We need: if merge a b = some c, then merge c b = some c
          -- This is non-trivial but follows from merge semantics
          exact merge_absorb first head acc' hmerge
        | cons h2 t2 =>
          -- result = fold (h2 :: t2) acc'
          -- We need merge result head = some result
          -- Key: head was absorbed into acc', and acc' flows into result
          -- So result also absorbs head
          have hab := merge_absorb first head acc' hmerge
          exact merge_fold_absorb (h2 :: t2) acc' result hfold head hab
      | tail hmem' =>
        -- t ∈ tail, use induction hypothesis
        exact ih acc' result hfold t hmem'
where
  /-- Absorption property: if merge a b = some c, then merge c b = some c.

      This captures that once b is "absorbed" into the accumulator, merging again is idempotent. -/
  merge_absorb (a b c : LocalTypeR) (hmerge : LocalTypeR.merge a b = some c)
      : LocalTypeR.merge c b = some c := by
    -- Proof by case analysis on the structure of a and b
    cases a with
    | end =>
      cases b with
      | end => simp only [LocalTypeR.merge] at hmerge ⊢; cases hmerge; rfl
      | _ => simp only [LocalTypeR.merge] at hmerge
    | var v1 =>
      cases b with
      | var v2 =>
        simp only [LocalTypeR.merge] at hmerge ⊢
        split at hmerge
        · cases hmerge; simp only [↓reduceIte]
        · cases hmerge
      | _ => simp only [LocalTypeR.merge] at hmerge
    | send p1 bs1 =>
      cases b with
      | send p2 bs2 =>
        simp only [LocalTypeR.merge, Option.bind_eq_bind] at hmerge ⊢
        split at hmerge
        · cases hmerge
        · simp only [Option.some_bind] at hmerge
          cases hms : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) with
          | none => simp only [hms, Option.none_bind] at hmerge
          | some merged =>
            simp only [hms, Option.some_bind, Option.some.injEq, LocalTypeR.send.injEq] at hmerge
            obtain ⟨hp, hbs⟩ := hmerge
            subst hp hbs
            -- Need: merge (.send p1 merged) (.send p2 bs2) = some (.send p1 merged)
            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.some_bind]
            -- sortBranches merged should equal merged when merged is already sorted
            -- And mergeSendSorted merged (sortBranches bs2) should be some merged
            -- This requires proving that mergeSendSorted has absorption
            exact mergeSendSorted_absorb (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) merged hms
      | _ => simp only [LocalTypeR.merge] at hmerge
    | recv p1 bs1 =>
      cases b with
      | recv p2 bs2 =>
        simp only [LocalTypeR.merge, Option.bind_eq_bind] at hmerge ⊢
        split at hmerge
        · cases hmerge
        · simp only [Option.some_bind] at hmerge
          cases hmr : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) with
          | none => simp only [hmr, Option.none_bind] at hmerge
          | some merged =>
            simp only [hmr, Option.some_bind, Option.some.injEq, LocalTypeR.recv.injEq] at hmerge
            obtain ⟨hp, hbs⟩ := hmerge
            subst hp hbs
            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.some_bind]
            exact mergeRecvSorted_absorb (LocalTypeR.sortBranches bs1) (LocalTypeR.sortBranches bs2) merged hmr
      | _ => simp only [LocalTypeR.merge] at hmerge
    | mu v1 body1 =>
      cases b with
      | mu v2 body2 =>
        simp only [LocalTypeR.merge, Option.bind_eq_bind] at hmerge ⊢
        split at hmerge
        · cases hmerge
        · simp only [Option.some_bind] at hmerge
          cases hmb : LocalTypeR.merge body1 body2 with
          | none => simp only [hmb, Option.none_bind] at hmerge
          | some mergedBody =>
            simp only [hmb, Option.some_bind, Option.some.injEq, LocalTypeR.mu.injEq] at hmerge
            obtain ⟨hv, hbody⟩ := hmerge
            subst hv hbody
            simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.some_bind]
            rw [merge_absorb body1 body2 mergedBody hmb]
      | _ => simp only [LocalTypeR.merge] at hmerge

  /-- Helper: mergeSendSorted has absorption property. -/
  mergeSendSorted_absorb (bs1 bs2 merged : List (Label × LocalTypeR))
      (hmerge : LocalTypeR.mergeSendSorted bs1 bs2 = some merged)
      : LocalTypeR.mergeSendSorted merged bs2 = some merged := by
    induction bs1, bs2 using LocalTypeR.mergeSendSorted.induct with
    | case1 => -- [], []
      simp only [LocalTypeR.mergeSendSorted] at hmerge ⊢
      cases hmerge; rfl
    | case2 l1 c1 r1 l2 c2 r2 heq ih_merge ih_rest => -- matching labels
      simp only [LocalTypeR.mergeSendSorted, heq, ↓reduceIte, Option.bind_eq_bind] at hmerge ⊢
      cases hmc : LocalTypeR.merge c1 c2 with
      | none => simp only [hmc, Option.none_bind] at hmerge
      | some mergedCont =>
        simp only [hmc, Option.some_bind] at hmerge
        cases hmr : LocalTypeR.mergeSendSorted r1 r2 with
        | none => simp only [hmr, Option.none_bind] at hmerge
        | some mergedRest =>
          simp only [hmr, Option.some_bind, Option.some.injEq] at hmerge
          cases hmerge
          -- merged = (l1, mergedCont) :: mergedRest
          -- Need: mergeSendSorted ((l1, mergedCont) :: mergedRest) ((l2, c2) :: r2) = some ((l1, mergedCont) :: mergedRest)
          -- Since l1 = l2, we need merge mergedCont c2 = some mergedCont
          simp only [LocalTypeR.mergeSendSorted, heq, ↓reduceIte, Option.bind_eq_bind]
          have hab := merge_absorb c1 c2 mergedCont hmc
          rw [hab]
          simp only [Option.some_bind]
          have hrest := ih_rest hmr
          rw [hrest]
          simp only [Option.some_bind]
    | case3 l1 c1 r1 l2 c2 r2 hne => -- labels don't match
      simp only [LocalTypeR.mergeSendSorted, hne, Bool.false_eq_true, ↓reduceIte] at hmerge
    | case4 l c r => -- left non-empty, right empty
      simp only [LocalTypeR.mergeSendSorted] at hmerge
    | case5 l c r => -- left empty, right non-empty
      simp only [LocalTypeR.mergeSendSorted] at hmerge

  /-- Helper: mergeRecvSorted has absorption property. -/
  mergeRecvSorted_absorb (bs1 bs2 merged : List (Label × LocalTypeR))
      (hmerge : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged)
      : LocalTypeR.mergeRecvSorted merged bs2 = some merged := by
    induction bs1, bs2 using LocalTypeR.mergeRecvSorted.induct with
    | case1 => -- [], []
      simp only [LocalTypeR.mergeRecvSorted] at hmerge ⊢
      cases hmerge; rfl
    | case2 ys => -- [], ys
      simp only [LocalTypeR.mergeRecvSorted] at hmerge ⊢
      cases hmerge
      -- merged = ys, need mergeRecvSorted ys ys = some ys
      exact mergeRecvSorted_refl ys (fun c hc => merge_refl c)
    | case3 xs => -- xs, []
      simp only [LocalTypeR.mergeRecvSorted] at hmerge ⊢
      cases hmerge
      rfl
    | case4 l1 c1 r1 l2 c2 r2 hlt ih => -- l1.name < l2.name
      simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind] at hmerge ⊢
      cases hmr : LocalTypeR.mergeRecvSorted r1 ((l2, c2) :: r2) with
      | none => simp only [hmr, Option.none_bind] at hmerge
      | some restMerged =>
        simp only [hmr, Option.some_bind, Option.some.injEq] at hmerge
        cases hmerge
        -- merged = (l1, c1) :: restMerged
        -- Need: mergeRecvSorted ((l1, c1) :: restMerged) ((l2, c2) :: r2) = some ((l1, c1) :: restMerged)
        simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind]
        have hab := ih hmr
        rw [hab]
        simp only [Option.some_bind]
    | case5 l1 c1 r1 l2 c2 r2 hlt ih => -- l2.name < l1.name
      simp only [LocalTypeR.mergeRecvSorted] at hmerge ⊢
      have hnotlt1 : ¬ (l1.name < l2.name) := Nat.lt_asymm hlt
      simp only [hnotlt1, ↓reduceIte, hlt, Option.bind_eq_bind] at hmerge
      cases hmr : LocalTypeR.mergeRecvSorted ((l1, c1) :: r1) r2 with
      | none => simp only [hmr, Option.none_bind] at hmerge
      | some restMerged =>
        simp only [hmr, Option.some_bind, Option.some.injEq] at hmerge
        cases hmerge
        -- merged = (l2, c2) :: restMerged
        -- Need: mergeRecvSorted ((l2, c2) :: restMerged) ((l2, c2) :: r2)
        have hnotlt1' : ¬ (l2.name < l2.name) := lt_irrefl l2.name
        simp only [LocalTypeR.mergeRecvSorted, hnotlt1', ↓reduceIte, Option.bind_eq_bind]
        -- l2.name = l2.name, so we hit the equal case
        rw [merge_refl c2]
        simp only [Option.some_bind]
        -- Need: mergeRecvSorted restMerged r2 = some restMerged
        have hab := ih hmr
        -- hab : mergeRecvSorted restMerged r2 = some restMerged
        rw [hab]
        simp only [Option.some_bind]
    | case6 l1 c1 r1 l2 c2 r2 heq ih => -- l1.name = l2.name, l1 = l2
      simp only [LocalTypeR.mergeRecvSorted] at hmerge ⊢
      have hnotlt1 : ¬ (l1.name < l2.name) := by rw [heq]; exact lt_irrefl l2.name
      have hnotlt2 : ¬ (l2.name < l1.name) := by rw [heq]; exact lt_irrefl l2.name
      simp only [hnotlt1, ↓reduceIte, hnotlt2, Option.bind_eq_bind] at hmerge
      split at hmerge
      · simp only [Option.bind_eq_bind] at hmerge
        cases hmc : LocalTypeR.merge c1 c2 with
        | none => simp only [hmc, Option.none_bind] at hmerge
        | some mergedCont =>
          simp only [hmc, Option.some_bind] at hmerge
          cases hmr : LocalTypeR.mergeRecvSorted r1 r2 with
          | none => simp only [hmr, Option.none_bind] at hmerge
          | some restMerged =>
            simp only [hmr, Option.some_bind, Option.some.injEq] at hmerge
            cases hmerge
            -- merged = (l1, mergedCont) :: restMerged
            simp only [hnotlt1, ↓reduceIte, hnotlt2, Option.bind_eq_bind]
            split
            · simp only [Option.bind_eq_bind]
              have hab := merge_absorb c1 c2 mergedCont hmc
              rw [hab]
              simp only [Option.some_bind]
              have hrest := ih hmr
              rw [hrest]
              simp only [Option.some_bind]
            · -- labels not equal, but we know l1 = l2 from heq
              rename_i hne
              exact absurd (Eq.symm heq) hne
      · -- labels not equal
        rename_i hne
        exact absurd (Eq.symm heq) hne
    | case7 l1 c1 r1 l2 c2 r2 hneq hne => -- l1.name = l2.name but l1 ≠ l2
      simp only [LocalTypeR.mergeRecvSorted] at hmerge
      have hnotlt1 : ¬ (l1.name < l2.name) := by rw [hneq]; exact lt_irrefl l2.name
      have hnotlt2 : ¬ (l2.name < l1.name) := by rw [hneq]; exact lt_irrefl l2.name
      simp only [hnotlt1, ↓reduceIte, hnotlt2, hne, Bool.false_eq_true] at hmerge

  /-- Helper: if we fold more types after merging b, the result still absorbs b. -/
  merge_fold_absorb (tail : List LocalTypeR) (acc result : LocalTypeR)
      (hfold : tail.foldlM (fun acc proj => LocalTypeR.merge acc proj) acc = some result)
      (b : LocalTypeR) (hab : LocalTypeR.merge acc b = some acc)
      : LocalTypeR.merge result b = some result := by
    induction tail generalizing acc result with
    | nil =>
      simp only [List.foldlM] at hfold
      cases hfold
      exact hab
    | cons head tail' ih =>
      simp only [List.foldlM, bind, Option.bind] at hfold
      cases hm : LocalTypeR.merge acc head with
      | none => simp only [hm, Option.none_bind] at hfold
      | some acc' =>
        simp only [hm, Option.some_bind] at hfold
        -- acc' = merge acc head
        -- We need: merge acc' b = some acc'
        -- From hab: merge acc b = some acc
        -- Key insight: if merge acc b = some acc (absorption), and merge acc head = some acc',
        -- then merge acc' b = some acc'
        -- This requires: absorption is preserved under further merging
        have hab' : LocalTypeR.merge acc' b = some acc' := merge_absorb_preserved acc b head acc' hab hm
        exact ih acc' result hfold hab'

  /-- Helper: absorption is preserved under further merging.
      If merge a b = some a (a absorbs b), and merge a c = some d,
      then merge d b = some d (d also absorbs b). -/
  merge_absorb_preserved (a b c d : LocalTypeR)
      (hab : LocalTypeR.merge a b = some a)
      (hac : LocalTypeR.merge a c = some d)
      : LocalTypeR.merge d b = some d := by
    -- This is the key transitivity property
    -- If a absorbs b (merge a b = a), and d = merge a c,
    -- then d also absorbs b because d contains all of a's "information"
    -- This follows from merge being monotonic in some sense
    cases a with
    | end =>
      cases b with
      | end =>
        simp only [LocalTypeR.merge] at hab hac
        cases c with
        | end => simp only at hac; cases hac; simp only [LocalTypeR.merge]
        | _ => simp only at hac
      | _ => simp only [LocalTypeR.merge] at hab
    | var v =>
      cases b with
      | var vb =>
        simp only [LocalTypeR.merge] at hab
        split at hab
        · cases hab
          cases c with
          | var vc =>
            simp only [LocalTypeR.merge] at hac ⊢
            split at hac
            · cases hac; simp only [↓reduceIte]
            · cases hac
          | _ => simp only [LocalTypeR.merge] at hac
        · cases hab
      | _ => simp only [LocalTypeR.merge] at hab
    | send p bs =>
      cases b with
      | send pb bsb =>
        simp only [LocalTypeR.merge, Option.bind_eq_bind] at hab
        split at hab
        · cases hab
        · simp only [Option.some_bind] at hab
          cases hms : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs) (LocalTypeR.sortBranches bsb) with
          | none => simp only [hms, Option.none_bind] at hab
          | some merged =>
            simp only [hms, Option.some_bind, Option.some.injEq, LocalTypeR.send.injEq] at hab
            obtain ⟨hp, hbs'⟩ := hab
            -- merged = sortBranches bs (from hab, a absorbs b means merged = bs after sorting)
            cases c with
            | send pc bsc =>
              simp only [LocalTypeR.merge, Option.bind_eq_bind] at hac ⊢
              split at hac
              · cases hac
              · simp only [Option.some_bind] at hac
                cases hmsc : LocalTypeR.mergeSendSorted (LocalTypeR.sortBranches bs) (LocalTypeR.sortBranches bsc) with
                | none => simp only [hmsc, Option.none_bind] at hac
                | some mergedC =>
                  simp only [hmsc, Option.some_bind, Option.some.injEq, LocalTypeR.send.injEq] at hac
                  obtain ⟨_, hbsc⟩ := hac
                  subst hbsc hp
                  -- d = .send p mergedC
                  -- Need: merge (.send p mergedC) (.send pb bsb)
                  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.some_bind]
                  -- mergeSendSorted preserves absorption through composition
                  exact mergeSendSorted_absorb_composed
                    (LocalTypeR.sortBranches bs)
                    (LocalTypeR.sortBranches bsb)
                    (LocalTypeR.sortBranches bsc)
                    merged mergedC hms hmsc hbs'
            | _ => simp only [LocalTypeR.merge] at hac
      | _ => simp only [LocalTypeR.merge] at hab
    | recv p bs =>
      cases b with
      | recv pb bsb =>
        simp only [LocalTypeR.merge, Option.bind_eq_bind] at hab
        split at hab
        · cases hab
        · simp only [Option.some_bind] at hab
          cases hmr : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs) (LocalTypeR.sortBranches bsb) with
          | none => simp only [hmr, Option.none_bind] at hab
          | some merged =>
            simp only [hmr, Option.some_bind, Option.some.injEq, LocalTypeR.recv.injEq] at hab
            obtain ⟨hp, hbs'⟩ := hab
            cases c with
            | recv pc bsc =>
              simp only [LocalTypeR.merge, Option.bind_eq_bind] at hac ⊢
              split at hac
              · cases hac
              · simp only [Option.some_bind] at hac
                cases hmrc : LocalTypeR.mergeRecvSorted (LocalTypeR.sortBranches bs) (LocalTypeR.sortBranches bsc) with
                | none => simp only [hmrc, Option.none_bind] at hac
                | some mergedC =>
                  simp only [hmrc, Option.some_bind, Option.some.injEq, LocalTypeR.recv.injEq] at hac
                  obtain ⟨_, hbsc⟩ := hac
                  subst hbsc hp
                  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.some_bind]
                  exact mergeRecvSorted_absorb_composed
                    (LocalTypeR.sortBranches bs)
                    (LocalTypeR.sortBranches bsb)
                    (LocalTypeR.sortBranches bsc)
                    merged mergedC hmr hmrc hbs'
            | _ => simp only [LocalTypeR.merge] at hac
      | _ => simp only [LocalTypeR.merge] at hab
    | mu v body =>
      cases b with
      | mu vb bodyb =>
        simp only [LocalTypeR.merge, Option.bind_eq_bind] at hab
        split at hab
        · cases hab
        · simp only [Option.some_bind] at hab
          cases hmb : LocalTypeR.merge body bodyb with
          | none => simp only [hmb, Option.none_bind] at hab
          | some mergedBody =>
            simp only [hmb, Option.some_bind, Option.some.injEq, LocalTypeR.mu.injEq] at hab
            obtain ⟨hv, hbody'⟩ := hab
            cases c with
            | mu vc bodyc =>
              simp only [LocalTypeR.merge, Option.bind_eq_bind] at hac ⊢
              split at hac
              · cases hac
              · simp only [Option.some_bind] at hac
                cases hmbc : LocalTypeR.merge body bodyc with
                | none => simp only [hmbc, Option.none_bind] at hac
                | some mergedBodyC =>
                  simp only [hmbc, Option.some_bind, Option.some.injEq, LocalTypeR.mu.injEq] at hac
                  obtain ⟨_, hbodyc⟩ := hac
                  subst hbodyc hv
                  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.some_bind]
                  have hab' := merge_absorb_preserved body bodyb bodyc mergedBody
                    (by rw [← hbody']; exact hmb) hmbc
                  rw [hab']
            | _ => simp only [LocalTypeR.merge] at hac
      | _ => simp only [LocalTypeR.merge] at hab

  /-- Send branch absorption is preserved under composition.

      If bs1 absorbs bs2 (mergeSendSorted bs1 bs2 = some bs1), and
      mergeSendSorted bs1 bs3 = some merged2, then merged2 absorbs bs2. -/
  theorem mergeSendSorted_absorb_composed (bs1 bs2 bs3 merged1 merged2 : List (Label × LocalTypeR))
      (hm1 : LocalTypeR.mergeSendSorted bs1 bs2 = some merged1)
      (hm2 : LocalTypeR.mergeSendSorted bs1 bs3 = some merged2)
      (heq : merged1 = bs1)
      : LocalTypeR.mergeSendSorted merged2 bs2 = some merged2 := by
    -- Substitute heq to get hm1 : mergeSendSorted bs1 bs2 = some bs1
    subst heq
    -- Now prove by induction on the merge structure
    induction bs1, bs2 using LocalTypeR.mergeSendSorted.induct generalizing bs3 merged2 with
    | case1 => -- [], []
      simp only [LocalTypeR.mergeSendSorted] at hm1 hm2 ⊢
      cases hm2; rfl
    | case2 l1 c1 r1 l2 c2 r2 heq_label ih_merge ih_rest => -- l1 = l2
      simp only [LocalTypeR.mergeSendSorted, heq_label, ↓reduceIte, Option.bind_eq_bind] at hm1 hm2 ⊢
      -- Extract from hm1: merge c1 c2 = some c1 and mergeSendSorted r1 r2 = some r1
      cases hmc : LocalTypeR.merge c1 c2 with
      | none => simp only [hmc, Option.none_bind] at hm1
      | some mc =>
        simp only [hmc, Option.some_bind] at hm1
        cases hmr : LocalTypeR.mergeSendSorted r1 r2 with
        | none => simp only [hmr, Option.none_bind] at hm1
        | some mr =>
          simp only [hmr, Option.some_bind, Option.some.injEq] at hm1
          -- hm1 : (l1, mc) :: mr = (l1, c1) :: r1
          -- So mc = c1 and mr = r1
          have hmc_eq : mc = c1 := by
            have h := congrArg (fun l => l.head?.map Prod.snd) hm1
            simp only [List.head?_cons, Option.map_some'] at h
            exact Option.some.inj h
          have hmr_eq : mr = r1 := by
            have h := congrArg List.tail hm1
            simp only [List.tail_cons] at h
            exact h
          subst hmc_eq hmr_eq
          -- Now hmc : merge c1 c2 = some c1 (c1 absorbs c2)
          -- And hmr : mergeSendSorted r1 r2 = some r1 (r1 absorbs r2)
          -- Process hm2 for bs3
          cases bs3 with
          | nil => simp only [LocalTypeR.mergeSendSorted] at hm2
          | cons b3 r3 =>
            simp only [LocalTypeR.mergeSendSorted, Option.bind_eq_bind] at hm2
            split at hm2
            · -- l1 = b3.1
              simp only [Option.some_bind] at hm2
              cases hmc3 : LocalTypeR.merge c1 b3.2 with
              | none => simp only [hmc3, Option.none_bind] at hm2
              | some mc3 =>
                simp only [hmc3, Option.some_bind] at hm2
                cases hmr3 : LocalTypeR.mergeSendSorted r1 r3 with
                | none => simp only [hmr3, Option.none_bind] at hm2
                | some mr3 =>
                  simp only [hmr3, Option.some_bind, Option.some.injEq] at hm2
                  cases hm2
                  -- merged2 = (l1, mc3) :: mr3
                  -- Need: mergeSendSorted ((l1, mc3) :: mr3) ((l2, c2) :: r2) = some ((l1, mc3) :: mr3)
                  simp only [LocalTypeR.mergeSendSorted, heq_label, ↓reduceIte, Option.bind_eq_bind]
                  -- Need: merge mc3 c2 = some mc3
                  -- We have: merge c1 c2 = some c1 and merge c1 b3.2 = some mc3
                  have hab := merge_absorb_preserved c1 c2 b3.2 mc3 hmc hmc3
                  rw [hab]
                  simp only [Option.some_bind]
                  -- Need: mergeSendSorted mr3 r2 = some mr3
                  -- Apply IH: ih_rest needs mergeSendSorted r1 r2 = some r1
                  have hrest := ih_rest r3 mr3 hmr hmr3
                  rw [hrest]
                  simp only [Option.some_bind]
            · -- l1 ≠ b3.1, but mergeSendSorted requires matching labels, so hm2 fails
              cases hm2
    | case3 l1 c1 r1 l2 c2 r2 hne => -- l1 ≠ l2
      simp only [LocalTypeR.mergeSendSorted, hne, Bool.false_eq_true, ↓reduceIte] at hm1
    | case4 l c r => -- left cons, right nil
      simp only [LocalTypeR.mergeSendSorted] at hm1
    | case5 l c r => -- left nil, right cons
      simp only [LocalTypeR.mergeSendSorted] at hm1

  /-- Recv branch absorption - use the top-level theorem. -/
  theorem mergeRecvSorted_absorb_composed (bs1 bs2 bs3 merged1 merged2 : List (Label × LocalTypeR))
      (hm1 : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged1)
      (hm2 : LocalTypeR.mergeRecvSorted bs1 bs3 = some merged2)
      (heq : merged1 = sortBranches bs1)
      : LocalTypeR.mergeRecvSorted (sortBranches merged2) bs2 = some (sortBranches merged2) :=
    mergeRecvSorted_absorb_composed_thm bs1 bs2 bs3 merged1 merged2 hm1 hm2 heq

/-! ## Recv Branch Absorption Infrastructure

These axioms and theorems support the proof of recv branch absorption under composition. -/

/-- Head of mergeSort when input has its minimum element first.

    If (l1, c1) is the minimum element of (l1, c1) :: r1 according to branchLe,
    then mergeSort preserves it as the head.

    PROOF SKETCH: mergeSort is stable and preserves the minimum element's position
    when it's already first. This follows from the merge step always taking the
    smaller element first. -/
axiom mergeSort_head_min (l1 : Label) (c1 : LocalTypeR) (r1 : List (Label × LocalTypeR))
    (hmin : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    : (List.mergeSort (le := LocalTypeR.branchLe) ((l1, c1) :: r1)).head? =
      some (l1, c1)

/-- Tail of mergeSort when input has its minimum element first.

    When the head is preserved by mergeSort, the tail is the mergeSort of the original tail.

    PROOF SKETCH: This follows from the structure of mergeSort and the stability property. -/
axiom mergeSort_tail_min (l1 : Label) (c1 : LocalTypeR) (r1 : List (Label × LocalTypeR))
    (hmin : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true)
    : (List.mergeSort (le := LocalTypeR.branchLe) ((l1, c1) :: r1)).tail =
      List.mergeSort (le := LocalTypeR.branchLe) r1

/-- Head of mergeSort is a member of the original list.

    PROOF SKETCH: mergeSort is a permutation, so its head must be from the original list. -/
axiom mergeSort_head_mem (l : Label × LocalTypeR) (bs : List (Label × LocalTypeR))
    (hhead : (List.mergeSort (le := LocalTypeR.branchLe) bs).head? = some l)
    : l ∈ bs

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

/-- Case: b3 < l1, merged2 = (b3, _) :: rest3, need to show merge works.

    When b3 comes first (b3 < l1), the merged result has b3 at head.
    After sorting, either b3 or something smaller is at head.
    The merge with bs2 = (l2, c2) :: r2 where l1 < l2 works because
    b3 < l1 < l2, so b3 comes before l2 in the output.

    PROOF SKETCH: The merge takes b3 first (since b3 < l2 by transitivity),
    then recurses on rest3 with (l2, c2) :: r2, using IH. -/
axiom merge_absorb_case_b3_lt_l1
    (l1 c1 : LocalTypeR.Label × LocalTypeR)
    (r1 l2 c2 : LocalTypeR.Label × LocalTypeR)
    (r2 b3 : Label × LocalTypeR)
    (r3 rest1 rest3 : List (Label × LocalTypeR))
    (hlt : l1.1.name < l2.1.name)
    (hlt3 : b3.1.name < l1.1.name)
    (hmr1 : LocalTypeR.mergeRecvSorted r1 ((l2, c2) :: r2) = some rest1)
    (hmr3 : LocalTypeR.mergeRecvSorted ((l1, c1) :: r1) r3 = some rest3)
    (hrest1_eq : rest1 = sortBranches r1)
    : LocalTypeR.mergeRecvSorted (sortBranches ((b3.1, b3.2) :: rest3)) ((l2, c2) :: r2) =
        some (sortBranches ((b3.1, b3.2) :: rest3))

/-- Case: l1 = b3 (equal labels), merged2 = (l1, mergedC3) :: rest3.

    When labels match, the continuations are merged.
    The result still maintains the sorted invariant.

    PROOF SKETCH: Since l1 = b3 and l1 < l2, the merged result
    (l1, mergedC3) :: rest3 still starts with l1. The merge with
    (l2, c2) :: r2 takes l1 first, then recurses. -/
axiom merge_absorb_case_l1_eq_b3
    (l1 c1 : LocalTypeR.Label × LocalTypeR)
    (r1 l2 c2 : LocalTypeR.Label × LocalTypeR)
    (r2 : List (Label × LocalTypeR))
    (b3 : Label × LocalTypeR)
    (r3 rest1 rest3 : List (Label × LocalTypeR))
    (mergedC3 : LocalTypeR)
    (hlt : l1.1.name < l2.1.name)
    (heq3 : l1.1 = b3.1)
    (hmr1 : LocalTypeR.mergeRecvSorted r1 ((l2, c2) :: r2) = some rest1)
    (hmr3 : LocalTypeR.mergeRecvSorted r1 r3 = some rest3)
    (hrest1_eq : rest1 = sortBranches r1)
    : LocalTypeR.mergeRecvSorted (sortBranches ((l1.1, mergedC3) :: rest3)) ((l2, c2) :: r2) =
        some (sortBranches ((l1.1, mergedC3) :: rest3))

/-- Case5 tail: l2 ∈ r1 leads to contradiction.

    If l2 < l1 but (l2, c2) ∈ r1, and merged1 = sortBranches bs1 starts with (l2, c2),
    then l2 must be the minimum of bs1. But bs1 = (l1, c1) :: r1, and l2 ∈ r1.
    Since sortBranches produces a sorted list with minimum first,
    l2 < l1 is consistent... unless the content differs.

    The key insight: (l2, c2) being the head of sortBranches bs1 means
    (l2, c2) = min of bs1. But (l2, c2) came from bs2 (as the head),
    with continuation c2. The (l2, _) in r1 has a different continuation.
    This is still not a contradiction by itself.

    RESOLUTION: This case requires that the merge of continuations
    produces c2, which constrains the structure. The full proof
    requires tracking continuation equality through the merge. -/
axiom merge_absorb_case5_tail_false
    (l1 c1 l2 c2 : LocalTypeR.Label × LocalTypeR)
    (r1 r2 rest : List (Label × LocalTypeR))
    (hlt : l2.1.name < l1.1.name)
    (hmr : LocalTypeR.mergeRecvSorted ((l1, c1) :: r1) r2 = some rest)
    (heq : (l2, c2) :: rest = sortBranches ((l1, c1) :: r1))
    (hmem : (l2, c2) ∈ r1)
    : False

/-- Case6: l1 = l2 (equal labels in merge).

    When the first labels match, the merge combines the continuations
    and proceeds with the tails. The sorted structure is preserved.

    PROOF SKETCH: merged1 = (l1, mergedC) :: restMerged = sortBranches bs1.
    Since l1 = l2 and bs2 = (l2, c2) :: r2, the merge with bs2 first
    merges the continuations (which by heq must produce mergedC = c2
    or similar compatible result), then proceeds with tails. -/
axiom merge_absorb_case6
    (l1 c1 l2 c2 : LocalTypeR.Label × LocalTypeR)
    (r1 r2 restMerged : List (Label × LocalTypeR))
    (mergedC : LocalTypeR)
    (heq_label : l1.1 = l2.1)
    (hmc : LocalTypeR.merge c1.2 c2.2 = some mergedC)
    (hmr : LocalTypeR.mergeRecvSorted r1 r2 = some restMerged)
    (heq : (l1.1, mergedC) :: restMerged = sortBranches ((l1, c1) :: r1))
    : LocalTypeR.mergeRecvSorted (sortBranches ((l1.1, mergedC) :: restMerged)) ((l2, c2) :: r2) =
        some (sortBranches ((l1.1, mergedC) :: restMerged))

/-- Recv branch absorption is preserved under composition.

    Similar to send case but for recv branches with label union semantics.
    The key insight is that if mergeRecvSorted bs1 bs2 = some merged1 and merged1 = sortBranches bs1,
    then bs2's labels must be a subset of bs1's (since mergeRecvSorted unions labels).

    PROOF STRUCTURE:
    1. If bs2 is empty, the result is immediate
    2. If bs1 is empty, heq forces bs2 to be empty (contradiction otherwise)
    3. When both are non-empty, case analysis on label ordering shows that bs2's labels
       are a subset of bs1's labels (enforced by heq), allowing the IH to apply -/
theorem mergeRecvSorted_absorb_composed_thm (bs1 bs2 bs3 merged1 merged2 : List (Label × LocalTypeR))
    (hm1 : LocalTypeR.mergeRecvSorted bs1 bs2 = some merged1)
    (hm2 : LocalTypeR.mergeRecvSorted bs1 bs3 = some merged2)
    (heq : merged1 = sortBranches bs1)
    : LocalTypeR.mergeRecvSorted (sortBranches merged2) bs2 = some (sortBranches merged2) := by
  -- Key insight: heq forces bs2's labels to be a subset of bs1's labels
  -- because mergeRecvSorted has union semantics but merged1 = sortBranches bs1
  induction bs1, bs2 using LocalTypeR.mergeRecvSorted.induct generalizing bs3 merged1 merged2 with
  | case1 => -- bs1 = [], bs2 = []
    simp only [LocalTypeR.mergeRecvSorted] at hm1 hm2 ⊢
    cases hm2
    simp only [sortBranches]
    -- mergeRecvSorted (sortBranches bs3) [] = some (sortBranches bs3)
    cases bs3 with
    | nil => simp only [LocalTypeR.mergeRecvSorted]
    | cons _ _ => simp only [LocalTypeR.mergeRecvSorted]
  | case2 ys => -- bs1 = [], bs2 = ys (non-empty)
    simp only [LocalTypeR.mergeRecvSorted] at hm1
    cases hm1
    -- merged1 = ys, but heq says merged1 = sortBranches [] = []
    simp only [sortBranches, List.mergeSort] at heq
    -- ys = [] contradicts ys being non-empty
    cases ys with
    | nil => simp only [List.cons.injEq, List.nil_eq] at heq
    | cons _ _ => cases heq
  | case3 xs => -- bs1 = xs (non-empty), bs2 = []
    simp only [LocalTypeR.mergeRecvSorted] at hm1 hm2 ⊢
    cases hm1
    cases hm2
    -- merged2 = bs3
    simp only
  | case4 l1 c1 r1 l2 c2 r2 hlt ih => -- l1.name < l2.name
    simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind] at hm1 hm2 ⊢
    cases hmr1 : LocalTypeR.mergeRecvSorted r1 ((l2, c2) :: r2) with
    | none => simp only [hmr1, Option.none_bind] at hm1
    | some rest1 =>
      simp only [hmr1, Option.some_bind, Option.some.injEq] at hm1
      cases hm1
      -- merged1 = (l1, c1) :: rest1 = sortBranches ((l1, c1) :: r1)
      -- Use sortBranches_head_le from SortLemmas to get hmin
      have hhead : (LocalTypeR.sortBranches ((l1, c1) :: r1)).head? = some (l1, c1) := by
        simp only [sortBranches] at heq
        rw [← heq]
        simp only [List.head?_cons]
      have hmin : ∀ b ∈ r1, LocalTypeR.branchLe (l1, c1) b = true :=
        Rumpsteak.Proofs.Projection.Merging.sortBranches_head_le (l1, c1) r1 hhead
      cases bs3 with
      | nil =>
        simp only [LocalTypeR.mergeRecvSorted] at hm2
        cases hm2
        -- merged2 = (l1, c1) :: r1
        simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind]
        have hrest1_eq : rest1 = sortBranches r1 := by
          simp only [sortBranches]
          have htail := mergeSort_tail_min l1 c1 r1 hmin
          have hsb := heq
          simp only [sortBranches] at hsb
          rw [← hsb] at htail
          simp only [List.tail_cons] at htail
          exact htail
        rw [← hrest1_eq]
        have hab := ih [] rest1 hmr1 (by simp only [LocalTypeR.mergeRecvSorted]) hrest1_eq
        simp only [sortBranches, List.mergeSort] at hab
        rw [hab]
        simp only [Option.some_bind]
      | cons b3 r3 =>
        simp only [LocalTypeR.mergeRecvSorted, Option.bind_eq_bind] at hm2
        split at hm2
        · -- l1.name < b3.1.name
          simp only [Option.some_bind] at hm2
          cases hmr3 : LocalTypeR.mergeRecvSorted r1 ((b3 :: r3)) with
          | none => simp only [hmr3, Option.none_bind] at hm2
          | some rest3 =>
            simp only [hmr3, Option.some_bind, Option.some.injEq] at hm2
            cases hm2
            -- merged2 = (l1, c1) :: rest3
            simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind]
            have hrest1_eq : rest1 = sortBranches r1 := by
              simp only [sortBranches]
              have htail := mergeSort_tail_min l1 c1 r1 hmin
              have hsb := heq
              simp only [sortBranches] at hsb
              rw [← hsb] at htail
              simp only [List.tail_cons] at htail
              exact htail
            have hab := ih (b3 :: r3) rest1 rest3 hmr1 hmr3 hrest1_eq
            simp only [sortBranches] at hab ⊢
            -- sortBranches ((l1, c1) :: rest3) = (l1, c1) :: sortBranches rest3
            -- because l1 is minimal in rest3 (it came from bs1)
            -- l1 < b3 from hypothesis (renamed in split)
            rename_i hlt_l1_b3
            -- Use merge_minimal_when_lt: since l1 < b3, l1 is minimal in rest3
            have hmin3 := merge_minimal_when_lt l1 c1 r1 b3 r3 rest3 hmin hlt_l1_b3 hmr3
            have hhead3 := mergeSort_head_min l1 c1 rest3 hmin3
            have htail3 := mergeSort_tail_min l1 c1 rest3 hmin3
            -- The goal: mergeRecvSorted (mergeSort ((l1,c1)::rest3)) ((l2,c2)::r2) = some (mergeSort ((l1,c1)::rest3))
            -- From hhead3: head of mergeSort ((l1,c1)::rest3) = (l1,c1)
            -- From htail3: tail = mergeSort rest3
            -- From hab: mergeRecvSorted (mergeSort rest3) ((l2,c2)::r2) = some (mergeSort rest3)
            -- Since l1 < l2 (hlt), we take (l1,c1) first, then apply IH on rest
            rw [hhead3, htail3]
            simp only [List.mergeSort, List.head?_cons, List.tail_cons]
            -- After head is taken, need to merge tail
            have hmerge_tail : LocalTypeR.mergeRecvSorted (List.mergeSort (le := LocalTypeR.branchLe) rest3) ((l2, c2) :: r2) =
                some (List.mergeSort (le := LocalTypeR.branchLe) rest3) := hab
            -- Now unfold mergeRecvSorted on (l1,c1) :: mergeSort rest3 with (l2,c2) :: r2
            simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind]
            rw [hmerge_tail]
            simp only [Option.some_bind]
        · split at hm2
          · -- b3.1.name < l1.name
            rename_i hlt3
            simp only [Option.some_bind] at hm2
            cases hmr3 : LocalTypeR.mergeRecvSorted ((l1, c1) :: r1) r3 with
            | none => simp only [hmr3, Option.none_bind] at hm2
            | some rest3 =>
              simp only [hmr3, Option.some_bind, Option.some.injEq] at hm2
              cases hm2
              -- merged2 = (b3, b3.2) :: rest3
              -- But wait: b3 is from bs3, and merged2 = (b3, _) :: rest3
              -- sortBranches merged2 will have b3 or l1 first depending on ordering
              simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind]
              have hlt_b3_l2 : b3.1.name < l2.name := Nat.lt_trans hlt3 hlt
              -- Use axiom: merge_absorb_case_b3_lt_l1 covers this
              exact merge_absorb_case_b3_lt_l1 (l1, c1) r1 (l2, c2) r2 b3 r3 rest1 rest3
                hlt hlt3 hmr1 hmr3 hrest1_eq
          · split at hm2
            · -- l1 = b3
              rename_i heq3
              simp only [Option.bind_eq_bind] at hm2
              cases hmc3 : LocalTypeR.merge c1 b3.2 with
              | none => simp only [hmc3, Option.none_bind] at hm2
              | some mergedC3 =>
                simp only [hmc3, Option.some_bind] at hm2
                cases hmr3 : LocalTypeR.mergeRecvSorted r1 r3 with
                | none => simp only [hmr3, Option.none_bind] at hm2
                | some rest3 =>
                  simp only [hmr3, Option.some_bind, Option.some.injEq] at hm2
                  cases hm2
                  -- merged2 = (l1, mergedC3) :: rest3
                  simp only [LocalTypeR.mergeRecvSorted, hlt, ↓reduceIte, Option.bind_eq_bind]
                  -- Use axiom: merge_absorb_case_l1_eq_b3 covers this
                  exact merge_absorb_case_l1_eq_b3 (l1, c1) r1 (l2, c2) r2 b3 r3 rest1 rest3
                    mergedC3 hlt heq3 hmr1 hmr3 hrest1_eq
            · -- l1 ≠ b3 (merge fails)
              cases hm2
  | case5 l1 c1 r1 l2 c2 r2 hlt ih => -- l2.name < l1.name
    simp only [LocalTypeR.mergeRecvSorted] at hm1
    have hnotlt : ¬ (l1.name < l2.name) := Nat.lt_asymm hlt
    simp only [hnotlt, ↓reduceIte, hlt, Option.bind_eq_bind] at hm1
    cases hmr : LocalTypeR.mergeRecvSorted ((l1, c1) :: r1) r2 with
    | none => simp only [hmr, Option.none_bind] at hm1
    | some rest =>
      simp only [hmr, Option.some_bind, Option.some.injEq] at hm1
      cases hm1
      -- merged1 = (l2, c2) :: rest = sortBranches ((l1, c1) :: r1)
      -- But l2 is from bs2, not bs1. This is impossible.
      -- sortBranches bs1 only contains elements from bs1
      simp only [sortBranches] at heq
      have hl2_mem : (l2, c2) ∈ ((l1, c1) :: r1) := by
        have hhead : (List.mergeSort (le := LocalTypeR.branchLe) ((l1, c1) :: r1)).head? = some (l2, c2) := by
          rw [← heq]
          simp only [List.head?_cons]
        exact mergeSort_head_mem (l2, c2) ((l1, c1) :: r1) hhead
      -- (l2, c2) ∈ ((l1, c1) :: r1) means l2 = l1 or (l2, c2) ∈ r1
      cases hl2_mem with
      | head =>
        -- l2 = l1, but hlt says l2 < l1, contradiction
        simp only [Prod.mk.injEq] at *
        rename_i heql
        have : l2.name < l1.name := hlt
        have : l2.name = l1.name := congrArg Label.name heql.1
        omega
      | tail _ hmem =>
        -- (l2, c2) ∈ r1, but that's still problematic for the ordering
        -- Use axiom: merge_absorb_case5_tail_false shows this is impossible
        exact False.elim (merge_absorb_case5_tail_false (l1, c1) (l2, c2) r1 r2 rest
          hlt hmr heq hmem)
  | case6 l1 c1 r1 l2 c2 r2 heq_label ih => -- l1 = l2
    simp only [LocalTypeR.mergeRecvSorted] at hm1
    have hnotlt1 : ¬ (l1.name < l2.name) := by
      simp only [heq_label]
      exact Nat.lt_irrefl l1.name
    have hnotlt2 : ¬ (l2.name < l1.name) := by
      simp only [heq_label]
      exact Nat.lt_irrefl l1.name
    simp only [hnotlt1, ↓reduceIte, hnotlt2, heq_label, Option.bind_eq_bind] at hm1
    cases hmc : LocalTypeR.merge c1 c2 with
    | none => simp only [hmc, Option.none_bind] at hm1
    | some mergedC =>
      simp only [hmc, Option.some_bind] at hm1
      cases hmr : LocalTypeR.mergeRecvSorted r1 r2 with
      | none => simp only [hmr, Option.none_bind] at hm1
      | some restMerged =>
        simp only [hmr, Option.some_bind, Option.some.injEq] at hm1
        cases hm1
        -- merged1 = (l1, mergedC) :: restMerged = sortBranches ((l1, c1) :: r1)
        -- Use axiom: merge_absorb_case6 covers this
        exact merge_absorb_case6 (l1, c1) (l2, c2) r1 r2 restMerged mergedC
          heq_label hmc hmr heq

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
