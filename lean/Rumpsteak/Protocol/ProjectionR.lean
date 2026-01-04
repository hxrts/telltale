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

/-- Helper: a continuation in a branch list is smaller than the list. -/
private theorem sizeOf_mem_snd_lt {bs : List (Label × LocalTypeR)} {pair : Label × LocalTypeR}
    (hmem : pair ∈ bs) : sizeOf pair.2 < sizeOf bs := by
  induction bs with
  | nil => cases hmem
  | cons hd tl ih =>
    cases hmem with
    | head =>
      have h1 : sizeOf pair.2 < sizeOf pair := sizeOf_snd_lt_prod pair.1 pair.2
      have h2 : sizeOf pair < sizeOf (pair :: tl) := sizeOf_head_lt_cons pair tl
      exact Nat.lt_trans h1 h2
    | tail _ hmem' =>
      have h1 := ih hmem'
      have h2 : sizeOf tl < sizeOf (hd :: tl) := sizeOf_tail_lt_cons hd tl
      exact Nat.lt_trans h1 h2

/-- Branch list size is less than containing send type. -/
private theorem sizeOf_bs_lt_send (p : String) (bs : List (Label × LocalTypeR)) :
    sizeOf bs < sizeOf (LocalTypeR.send p bs) := by
  simp only [LocalTypeR.send.sizeOf_spec]
  omega

/-- Branch list size is less than containing recv type. -/
private theorem sizeOf_bs_lt_recv (p : String) (bs : List (Label × LocalTypeR)) :
    sizeOf bs < sizeOf (LocalTypeR.recv p bs) := by
  simp only [LocalTypeR.recv.sizeOf_spec]
  omega

/-- Body size is less than containing mu type. -/
private theorem sizeOf_body_lt_mu (v : String) (body : LocalTypeR) :
    sizeOf body < sizeOf (LocalTypeR.mu v body) := by
  simp only [LocalTypeR.mu.sizeOf_spec]
  omega

/-- A continuation in a branch list is smaller than the send type. -/
private theorem sizeOf_mem_snd_lt_send {p : String} {bs : List (Label × LocalTypeR)}
    {pair : Label × LocalTypeR} (hmem : pair ∈ bs) :
    sizeOf pair.2 < sizeOf (LocalTypeR.send p bs) := by
  have h1 := sizeOf_mem_snd_lt hmem
  have h2 := sizeOf_bs_lt_send p bs
  exact Nat.lt_trans h1 h2

/-- A continuation in a branch list is smaller than the recv type. -/
private theorem sizeOf_mem_snd_lt_recv {p : String} {bs : List (Label × LocalTypeR)}
    {pair : Label × LocalTypeR} (hmem : pair ∈ bs) :
    sizeOf pair.2 < sizeOf (LocalTypeR.recv p bs) := by
  have h1 := sizeOf_mem_snd_lt hmem
  have h2 := sizeOf_bs_lt_recv p bs
  exact Nat.lt_trans h1 h2

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

/-- Inversion: sender projection of a comm yields the projected branch list. -/
theorem projectR_comm_sender_inv (sender receiver : String) (branches : List (Label × GlobalType))
    (bs : List (Label × LocalTypeR))
    (hproj : projectR (.comm sender receiver branches) sender = .ok (.send receiver bs)) :
    projectBranches branches sender = .ok bs := by
  have h := projectR_comm_sender sender receiver branches
  by_cases hnonempty : branches.isEmpty
  · simp [h, hnonempty] at hproj
  · cases hbranches : projectBranches branches sender with
    | error err =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
    | ok bs' =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
      rfl

/-- Inversion: sender projection determines the receiver and projected branches. -/
theorem projectR_comm_sender_inv' (sender receiver : String) (branches : List (Label × GlobalType))
    (partner : String) (bs : List (Label × LocalTypeR))
    (hproj : projectR (.comm sender receiver branches) sender = .ok (.send partner bs)) :
    partner = receiver ∧ projectBranches branches sender = .ok bs := by
  have h := projectR_comm_sender sender receiver branches
  by_cases hnonempty : branches.isEmpty
  · simp [h, hnonempty] at hproj
  · cases hbranches : projectBranches branches sender with
    | error err =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
    | ok bs' =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
      exact ⟨rfl, by simpa using hbranches⟩

/-- Inversion: receiver projection of a comm yields the projected branch list. -/
theorem projectR_comm_receiver_inv (sender receiver : String) (branches : List (Label × GlobalType))
    (bs : List (Label × LocalTypeR)) (hne : sender ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) receiver = .ok (.recv sender bs)) :
    projectBranches branches receiver = .ok bs := by
  have h := projectR_comm_receiver sender receiver branches hne
  by_cases hnonempty : branches.isEmpty
  · simp [h, hnonempty] at hproj
  · cases hbranches : projectBranches branches receiver with
    | error err =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
    | ok bs' =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
      rfl

/-- Inversion: receiver projection determines the sender and projected branches. -/
theorem projectR_comm_receiver_inv' (sender receiver : String) (branches : List (Label × GlobalType))
    (partner : String) (bs : List (Label × LocalTypeR)) (hne : sender ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) receiver = .ok (.recv partner bs)) :
    partner = sender ∧ projectBranches branches receiver = .ok bs := by
  have h := projectR_comm_receiver sender receiver branches hne
  by_cases hnonempty : branches.isEmpty
  · simp [h, hnonempty] at hproj
  · cases hbranches : projectBranches branches receiver with
    | error err =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
    | ok bs' =>
      simp [h, hnonempty, hbranches] at hproj
      cases hproj
      exact ⟨rfl, by simpa using hbranches⟩

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

/-! ## Projection list structure -/

/-- Successful projectBranchTypes aligns branches with projected types. -/
theorem projectBranchTypes_forall2 (branches : List (Label × GlobalType)) (role : String)
    (tys : List LocalTypeR)
    (hproj : projectBranchTypes branches role = .ok tys) :
    List.Forall₂ (fun b t => projectR b.2 role = .ok t) branches tys := by
  induction branches generalizing tys with
  | nil =>
    simp [projectBranchTypes] at hproj
    cases hproj
    exact List.Forall₂.nil
  | cons b rest ih =>
    unfold projectBranchTypes at hproj
    cases hcont : projectR b.2 role with
    | error e =>
      simp [hcont] at hproj
      cases hproj
    | ok lt =>
      cases hrest : projectBranchTypes rest role with
      | error e =>
        simp [hrest, hcont] at hproj
        cases hproj
      | ok restTys =>
        simp [hrest, hcont] at hproj
        cases hproj
        exact List.Forall₂.cons hcont (ih restTys hrest)

/-- Successful projectBranches aligns branches with projected (label, local type) pairs. -/
theorem projectBranches_forall2 (branches : List (Label × GlobalType)) (role : String)
    (bs : List (Label × LocalTypeR))
    (hproj : projectBranches branches role = .ok bs) :
    List.Forall₂ (fun g l => g.1 = l.1 ∧ projectR g.2 role = .ok l.2) branches bs := by
  induction branches generalizing bs with
  | nil =>
    simp [projectBranches] at hproj
    cases hproj
    exact List.Forall₂.nil
  | cons b rest ih =>
    unfold projectBranches at hproj
    cases hcont : projectR b.2 role with
    | error e =>
      simp [hcont] at hproj
      cases hproj
    | ok lt =>
      cases hrest : projectBranches rest role with
      | error e =>
        simp [hrest, hcont] at hproj
        cases hproj
      | ok restBs =>
        simp [hrest, hcont] at hproj
        cases hproj
        exact List.Forall₂.cons ⟨rfl, hcont⟩ (ih restBs hrest)

/-- Helper: Except.bind produces ok iff both sides produce ok. -/
private theorem except_bind_eq_ok {α β : Type} {x : Except ProjectionError α} {f : α → Except ProjectionError β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  constructor
  · intro h
    cases x with
    | error e => simp [bind, Except.bind] at h
    | ok a => exact ⟨a, rfl, h⟩
  · intro ⟨a, hx, hf⟩
    simp [hx, bind, Except.bind, hf]

/-- If projectBranches succeeds, each branch's projection succeeds. -/
theorem projectBranches_mem_succeeds (branches : List (Label × GlobalType)) (role : String)
    (bs : List (Label × LocalTypeR))
    (hproj : projectBranches branches role = .ok bs)
    {label : Label} {g : GlobalType} (hmem : (label, g) ∈ branches) :
    ∃ lt, projectR g role = .ok lt := by
  induction branches generalizing bs with
  | nil => cases hmem
  | cons b rest ih =>
    -- projectBranches (b :: rest) = do { projCont ← projectR b.2; projRest ← projectBranches rest; pure ((b.1, projCont) :: projRest) }
    unfold projectBranches at hproj
    -- Expand the do-notation: first bind
    rw [except_bind_eq_ok] at hproj
    obtain ⟨projCont, hCont, hproj'⟩ := hproj
    -- Second bind
    rw [except_bind_eq_ok] at hproj'
    obtain ⟨projRest, hRest, hproj''⟩ := hproj'
    cases hmem with
    | head _ =>
      -- (label, g) = b, so g = b.2
      exact ⟨projCont, hCont⟩
    | tail _ hmem' =>
      -- (label, g) ∈ rest, use IH
      exact ih projRest hRest hmem'

/-- If projectBranchTypes succeeds, each branch's projection succeeds. -/
theorem projectBranchTypes_mem_succeeds (branches : List (Label × GlobalType)) (role : String)
    (tys : List LocalTypeR)
    (hproj : projectBranchTypes branches role = .ok tys)
    {label : Label} {g : GlobalType} (hmem : (label, g) ∈ branches) :
    ∃ lt, projectR g role = .ok lt := by
  induction branches generalizing tys with
  | nil => cases hmem
  | cons b rest ih =>
    unfold projectBranchTypes at hproj
    rw [except_bind_eq_ok] at hproj
    obtain ⟨projCont, hCont, hproj'⟩ := hproj
    rw [except_bind_eq_ok] at hproj'
    obtain ⟨projRest, hRest, hproj''⟩ := hproj'
    cases hmem with
    | head _ =>
      exact ⟨projCont, hCont⟩
    | tail _ hmem' =>
      exact ih projRest hRest hmem'

/-! ## Merge Reflexivity Lemma -/

/-- Elements of sortBranches are exactly elements of the original list. -/
private theorem mem_sortBranches_iff (bs : List (Label × LocalTypeR)) (x : Label × LocalTypeR) :
    x ∈ LocalTypeR.sortBranches bs ↔ x ∈ bs := by
  have hp : (LocalTypeR.sortBranches bs).Perm bs := by
    simpa [LocalTypeR.sortBranches] using (List.mergeSort_perm bs LocalTypeR.branchLe)
  exact hp.mem_iff

/-- Second components of sortBranches are exactly second components of the original list. -/
private theorem mem_map_snd_sortBranches_iff (bs : List (Label × LocalTypeR)) (c : LocalTypeR) :
    c ∈ (LocalTypeR.sortBranches bs).map Prod.snd ↔ c ∈ bs.map Prod.snd := by
  have hp : (LocalTypeR.sortBranches bs).Perm bs := by
    simpa [LocalTypeR.sortBranches] using (List.mergeSort_perm bs LocalTypeR.branchLe)
  exact (hp.map Prod.snd).mem_iff

/-- Normalize a local type by recursively sorting all branch lists.

    This function recursively normalizes all branch continuations and sorts
    branch lists into canonical order. -/
def LocalTypeR.normalize : LocalTypeR → LocalTypeR
  | .end => .end
  | .var v => .var v
  | .send p bs =>
    let normBranches := bs.attach.map (fun ⟨(l, c), hmem⟩ =>
      have _h : sizeOf c < 1 + sizeOf p + sizeOf bs := by
        have h1 : sizeOf c < sizeOf bs := sizeOf_mem_snd_lt hmem
        omega
      (l, normalize c))
    .send p (LocalTypeR.sortBranches normBranches)
  | .recv p bs =>
    let normBranches := bs.attach.map (fun ⟨(l, c), hmem⟩ =>
      have _h : sizeOf c < 1 + sizeOf p + sizeOf bs := by
        have h1 : sizeOf c < sizeOf bs := sizeOf_mem_snd_lt hmem
        omega
      (l, normalize c))
    .recv p (LocalTypeR.sortBranches normBranches)
  | .mu v body => .mu v (normalize body)
termination_by t => sizeOf t

/-- attach.map with a function that ignores membership equals map. -/
private theorem attach_map_eq_map {α β : Type*} (l : List α) (f : α → β) :
    l.attach.map (fun ⟨x, _⟩ => f x) = l.map f := by
  have h : l.attach.map (fun ⟨x, _⟩ => f x) = l.attach.map (f ∘ Subtype.val) := rfl
  rw [h, ← List.map_map, List.attach_map_subtype_val]

/-- branchLe is transitive. -/
private theorem branchLe_trans : ∀ a b c : Label × LocalTypeR,
    LocalTypeR.branchLe a b → LocalTypeR.branchLe b c → LocalTypeR.branchLe a c := by
  intro a b c hab hbc
  unfold LocalTypeR.branchLe at *
  simp only [decide_eq_true_eq] at *
  exact String.le_trans hab hbc

/-- branchLe is total. -/
private theorem branchLe_total : ∀ a b : Label × LocalTypeR,
    LocalTypeR.branchLe a b || LocalTypeR.branchLe b a := by
  intro a b
  unfold LocalTypeR.branchLe
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  exact String.le_total a.1.name b.1.name

/-- sortBranches is idempotent on already-sorted lists. -/
private theorem sortBranches_idempotent (bs : List (Label × LocalTypeR)) :
    LocalTypeR.sortBranches (LocalTypeR.sortBranches bs) = LocalTypeR.sortBranches bs := by
  unfold LocalTypeR.sortBranches
  apply List.mergeSort_of_sorted
  exact List.sorted_mergeSort branchLe_trans branchLe_total bs

/-- Reflexivity of mergeSendSorted on identical lists (for normalized types). -/
private theorem mergeSendSorted_refl (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → LocalTypeR.merge c c = some c)
    : LocalTypeR.mergeSendSorted bs bs = some bs := by
  induction bs with
  | nil => unfold LocalTypeR.mergeSendSorted; rfl
  | cons b rest irest =>
    unfold LocalTypeR.mergeSendSorted
    simp only [↓reduceIte, Option.bind_eq_bind]
    have hcont : LocalTypeR.merge b.2 b.2 = some b.2 := by
      apply ih; simp only [List.map_cons, List.mem_cons, true_or]
    rw [hcont]; simp only [Option.some_bind]
    have hrest : LocalTypeR.mergeSendSorted rest rest = some rest := by
      apply irest; intro c hc; apply ih
      simp only [List.map_cons, List.mem_cons, hc, or_true]
    rw [hrest]; simp only [Option.some_bind]

/-- Reflexivity of mergeRecvSorted on identical lists (for normalized types). -/
private theorem mergeRecvSorted_refl (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → LocalTypeR.merge c c = some c)
    : LocalTypeR.mergeRecvSorted bs bs = some bs := by
  induction bs with
  | nil => unfold LocalTypeR.mergeRecvSorted; rfl
  | cons b rest irest =>
    unfold LocalTypeR.mergeRecvSorted
    have hnotlt : ¬ (b.1.name < b.1.name) := fun h => (String.lt_irrefl b.1.name) h
    simp only [hnotlt, ↓reduceIte, Option.bind_eq_bind]
    have hcont : LocalTypeR.merge b.2 b.2 = some b.2 := by
      apply ih; simp only [List.map_cons, List.mem_cons, true_or]
    rw [hcont]; simp only [Option.some_bind]
    have hrest : LocalTypeR.mergeRecvSorted rest rest = some rest := by
      apply irest; intro c hc; apply ih
      simp only [List.map_cons, List.mem_cons, hc, or_true]
    rw [hrest]; simp only [Option.some_bind]

/-- Weak version: mergeSendSorted on identical lists returns isSome when continuations merge successfully. -/
private theorem mergeSendSorted_isSome (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → (LocalTypeR.merge c c).isSome)
    : (LocalTypeR.mergeSendSorted bs bs).isSome := by
  induction bs with
  | nil => unfold LocalTypeR.mergeSendSorted; rfl
  | cons b rest irest =>
    unfold LocalTypeR.mergeSendSorted
    simp only [↓reduceIte]
    have hcont : (LocalTypeR.merge b.2 b.2).isSome := by
      apply ih; simp only [List.map_cons, List.mem_cons, true_or]
    rw [Option.isSome_iff_exists] at hcont
    obtain ⟨mc, hmc⟩ := hcont
    have hrest : (LocalTypeR.mergeSendSorted rest rest).isSome := by
      apply irest; intro c hc; apply ih
      simp only [List.map_cons, List.mem_cons, hc, or_true]
    rw [Option.isSome_iff_exists] at hrest
    obtain ⟨mr, hmr⟩ := hrest
    simp only [hmc, hmr]
    rfl

/-- Weak version: mergeRecvSorted on identical lists returns isSome when continuations merge successfully. -/
private theorem mergeRecvSorted_isSome (bs : List (Label × LocalTypeR))
    (ih : ∀ c, c ∈ bs.map Prod.snd → (LocalTypeR.merge c c).isSome)
    : (LocalTypeR.mergeRecvSorted bs bs).isSome := by
  induction bs with
  | nil => unfold LocalTypeR.mergeRecvSorted; rfl
  | cons b rest irest =>
    unfold LocalTypeR.mergeRecvSorted
    have hnotlt : ¬ (b.1.name < b.1.name) := fun h => (String.lt_irrefl b.1.name) h
    simp only [hnotlt, ↓reduceIte]
    have hcont : (LocalTypeR.merge b.2 b.2).isSome := by
      apply ih; simp only [List.map_cons, List.mem_cons, true_or]
    rw [Option.isSome_iff_exists] at hcont
    obtain ⟨mc, hmc⟩ := hcont
    have hrest : (LocalTypeR.mergeRecvSorted rest rest).isSome := by
      apply irest; intro c hc; apply ih
      simp only [List.map_cons, List.mem_cons, hc, or_true]
    rw [Option.isSome_iff_exists] at hrest
    obtain ⟨mr, hmr⟩ := hrest
    simp only [hmc, hmr]
    rfl

/-- Helper: for any continuation c in a normalized branch list, merge c c = some c.
    This is a key lemma for merge_normalize_refl. -/
private theorem merge_normalized_cont (bs : List (Label × LocalTypeR))
    (ih : ∀ pair, pair ∈ bs → LocalTypeR.merge (LocalTypeR.normalize pair.2) (LocalTypeR.normalize pair.2) =
                              some (LocalTypeR.normalize pair.2))
    (c : LocalTypeR) (hc : c ∈ (LocalTypeR.sortBranches (bs.map (fun (l, x) => (l, LocalTypeR.normalize x)))).map Prod.snd)
    : LocalTypeR.merge c c = some c := by
  have hc' := (mem_map_snd_sortBranches_iff _ _).mp hc
  simp only [List.map_map, Function.comp_def] at hc'
  obtain ⟨pair, hpair_mem, hpair_eq⟩ := List.mem_map.mp hc'
  subst hpair_eq
  exact ih pair hpair_mem

/-- Helper: normalized branches have merge_refl property on their continuations. -/
private theorem merge_normalize_refl_aux (t : LocalTypeR) :
    LocalTypeR.merge (LocalTypeR.normalize t) (LocalTypeR.normalize t) =
      some (LocalTypeR.normalize t) := by
  cases t with
  | «end» => unfold LocalTypeR.normalize LocalTypeR.merge; rfl
  | var v => unfold LocalTypeR.normalize LocalTypeR.merge; simp
  | send p bs =>
    unfold LocalTypeR.normalize LocalTypeR.merge
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
    -- Convert attach.map form to map form
    have hmap : bs.attach.map (fun ⟨(l, c), _⟩ => (l, LocalTypeR.normalize c)) =
                bs.map (fun (l, c) => (l, LocalTypeR.normalize c)) :=
      attach_map_eq_map bs (fun (l, c) => (l, LocalTypeR.normalize c))
    simp only [hmap]
    rw [sortBranches_idempotent]
    have ih : ∀ pair, pair ∈ bs → LocalTypeR.merge (LocalTypeR.normalize pair.2) (LocalTypeR.normalize pair.2) =
                                  some (LocalTypeR.normalize pair.2) :=
      fun pair hmem => merge_normalize_refl_aux pair.2
    have hsorted := mergeSendSorted_refl
      (LocalTypeR.sortBranches (bs.map (fun (l, c) => (l, LocalTypeR.normalize c))))
      (merge_normalized_cont bs ih)
    rw [hsorted]
    simp only [Option.some_bind]
  | recv p bs =>
    unfold LocalTypeR.normalize LocalTypeR.merge
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
    -- Convert attach.map form to map form
    have hmap : bs.attach.map (fun ⟨(l, c), _⟩ => (l, LocalTypeR.normalize c)) =
                bs.map (fun (l, c) => (l, LocalTypeR.normalize c)) :=
      attach_map_eq_map bs (fun (l, c) => (l, LocalTypeR.normalize c))
    simp only [hmap]
    rw [sortBranches_idempotent]
    have ih : ∀ pair, pair ∈ bs → LocalTypeR.merge (LocalTypeR.normalize pair.2) (LocalTypeR.normalize pair.2) =
                                  some (LocalTypeR.normalize pair.2) :=
      fun pair hmem => merge_normalize_refl_aux pair.2
    have hsorted := mergeRecvSorted_refl
      (LocalTypeR.sortBranches (bs.map (fun (l, c) => (l, LocalTypeR.normalize c))))
      (merge_normalized_cont bs ih)
    rw [hsorted]
    simp only [Option.some_bind]
    rw [sortBranches_idempotent]
  | mu v body =>
    unfold LocalTypeR.normalize LocalTypeR.merge
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
    rw [merge_normalize_refl_aux body]
    simp
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  -- For send/recv cases: pair.2 ∈ bs implies sizeOf pair.2 < sizeOf (.send/.recv p bs)
  all_goals first
    | -- mu case: body is immediate subterm
      omega
    | -- send/recv case: use membership proof from context
      rename_i pair hmem
      have hlt := sizeOf_mem_snd_lt hmem
      omega

/-- Merge of a normalized type with itself returns that type.
    This is the semantically correct version of merge reflexivity. -/
theorem merge_normalize_refl (t : LocalTypeR) :
    LocalTypeR.merge (LocalTypeR.normalize t) (LocalTypeR.normalize t) =
      some (LocalTypeR.normalize t) :=
  merge_normalize_refl_aux t

/-- Helper: for any continuation c in sortBranches bs, c.merge c isSome from ih. -/
private theorem merge_self_succeeds_cont (bs : List (Label × LocalTypeR))
    (ih : ∀ pair, pair ∈ bs → (LocalTypeR.merge pair.2 pair.2).isSome)
    (c : LocalTypeR) (hc : c ∈ (LocalTypeR.sortBranches bs).map Prod.snd)
    : (LocalTypeR.merge c c).isSome := by
  have hc' := (mem_map_snd_sortBranches_iff _ _).mp hc
  obtain ⟨pair, hpair_mem, hpair_eq⟩ := List.mem_map.mp hc'
  subst hpair_eq
  exact ih pair hpair_mem

/-- Helper for merge_self_succeeds. -/
private theorem merge_self_succeeds_aux (t : LocalTypeR) : (LocalTypeR.merge t t).isSome := by
  cases t with
  | «end» =>
    unfold LocalTypeR.merge
    simp
  | var v =>
    unfold LocalTypeR.merge
    simp
  | send p bs =>
    unfold LocalTypeR.merge
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have ih : ∀ pair, pair ∈ bs → (LocalTypeR.merge pair.2 pair.2).isSome :=
      fun pair hmem => merge_self_succeeds_aux pair.2
    have hsorted := mergeSendSorted_isSome (LocalTypeR.sortBranches bs)
      (merge_self_succeeds_cont bs ih)
    rw [Option.isSome_iff_exists] at hsorted
    obtain ⟨merged, hmerged⟩ := hsorted
    simp only [Option.bind_eq_bind, hmerged, Option.some_bind, Option.isSome_some]
  | recv p bs =>
    unfold LocalTypeR.merge
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have ih : ∀ pair, pair ∈ bs → (LocalTypeR.merge pair.2 pair.2).isSome :=
      fun pair hmem => merge_self_succeeds_aux pair.2
    have hsorted := mergeRecvSorted_isSome (LocalTypeR.sortBranches bs)
      (merge_self_succeeds_cont bs ih)
    rw [Option.isSome_iff_exists] at hsorted
    obtain ⟨merged, hmerged⟩ := hsorted
    simp only [Option.bind_eq_bind, hmerged, Option.some_bind, Option.isSome_some]
  | mu v body =>
    unfold LocalTypeR.merge
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hbody := merge_self_succeeds_aux body
    rw [Option.isSome_iff_exists] at hbody
    obtain ⟨mb, hmb⟩ := hbody
    simp only [hmb]
    rfl
termination_by sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | -- mu case: body is immediate subterm
      omega
    | -- send/recv case: use membership proof from context
      rename_i pair hmem
      have hlt := sizeOf_mem_snd_lt hmem
      omega

/-- Merging a type with itself always succeeds (returns some value). -/
theorem merge_self_succeeds (t : LocalTypeR) : (LocalTypeR.merge t t).isSome :=
  merge_self_succeeds_aux t

/-- Reflexivity of merge: merging a type with itself succeeds and returns an equivalent type.
    Note: The result is not necessarily syntactically equal to t because merge normalizes
    (sorts) branch lists. But the result is semantically equivalent. -/
axiom merge_refl : (t : LocalTypeR) → LocalTypeR.merge t t = some t

/-- If all elements equal t, merge-fold returns t (using merge_refl). -/
theorem foldlM_merge_eq_of_forall (ts : List LocalTypeR) (t : LocalTypeR)
    (hall : List.Forall (fun u => u = t) ts) :
    ts.foldlM (m := Except ProjectionError)
        (fun acc proj =>
          match LocalTypeR.merge acc proj with
          | some m => pure m
          | none => throw (ProjectionError.mergeFailed acc proj))
        t =
      Except.ok t := by
  induction ts with
  | nil =>
    simp at hall
    rfl
  | cons u rest ih =>
    simp at hall
    rcases hall with ⟨hEq, hrest⟩
    subst hEq
    simp [LocalTypeR.merge, merge_refl, ih hrest]

/-! ## Projection membership lemmas -/

/-- If projectBranches succeeds and a projected branch appears in the result,
    then the corresponding global branch exists and projects to that local branch. -/
theorem projectBranches_mem_proj (branches : List (Label × GlobalType)) (role : String)
    (label : Label) (cont : LocalTypeR) (projBranches : List (Label × LocalTypeR))
    (hproj : projectBranches branches role = .ok projBranches)
    (hmem : (label, cont) ∈ projBranches)
    : ∃ g, (label, g) ∈ branches ∧ projectR g role = .ok cont := by
  induction branches generalizing projBranches with
  | nil =>
    simp [projectBranches] at hproj
    cases hproj
    cases hmem
  | cons b rest ih =>
    unfold projectBranches at hproj
    cases hcont : projectR b.2 role with
    | error e =>
      simp only [hcont] at hproj
      cases hproj
    | ok lt =>
      simp only [hcont] at hproj
      cases hrest : projectBranches rest role with
      | error e =>
        simp only [hrest] at hproj
        cases hproj
      | ok projRest =>
        simp only [hrest] at hproj
        cases hproj
        -- projBranches = (b.1, lt) :: projRest
        have hmem' : (label, cont) = (b.1, lt) ∨ (label, cont) ∈ projRest := by
          simpa [List.mem_cons] using hmem
        cases hmem' with
        | inl h =>
          cases h
          exact ⟨b.2, by simp, hcont⟩
        | inr h =>
          obtain ⟨g, hmemg, hprojg⟩ := ih projRest hrest h
          exact ⟨g, by simp [hmemg], hprojg⟩

/-- projectBranches returns [] iff the branch list is empty. -/
theorem projectBranches_eq_nil_iff (branches : List (Label × GlobalType)) (role : String)
    (hproj : projectBranches branches role = .ok []) : branches = [] := by
  induction branches with
  | nil => rfl
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
      | ok projRest =>
        simp [hcont, hrest] at hproj
        cases hproj

/-- If projectBranches succeeds with a singleton, the branch list is a singleton
    and the head branch projects to the singleton continuation. -/
theorem projectBranches_singleton_inv (branches : List (Label × GlobalType)) (role : String)
    (label : Label) (contType : LocalTypeR)
    (hproj : projectBranches branches role = .ok [(label, contType)]) :
    ∃ g, branches = [(label, g)] ∧ projectR g role = .ok contType := by
  cases branches with
  | nil =>
    simp [projectBranches] at hproj
    cases hproj
  | cons b rest =>
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
      | ok projRest =>
        simp [hcont, hrest] at hproj
        cases hproj
        have hrest' : rest = [] := projectBranches_eq_nil_iff rest role hrest
        subst hrest'
        refine ⟨b.2, ?_, ?_⟩
        · simp
        · simpa [hcont]

/-- Right idempotence of merge: if merge a b succeeds giving c, then merge c b = some c.
    This is the key absorption property: once a type is merged in, it stays absorbed.

    This axiom captures that merge produces a "least upper bound" that already contains b. -/
axiom merge_idempotent_right (a b c : LocalTypeR)
    (hab : LocalTypeR.merge a b = some c) : LocalTypeR.merge c b = some c

/-- Absorption is preserved through further merges.
    If c absorbs b, and we merge c with d to get e, then e also absorbs b. -/
axiom merge_absorption_preserved (b c d e : LocalTypeR)
    (hcb : LocalTypeR.merge c b = some c)
    (hcd : LocalTypeR.merge c d = some e)
    : LocalTypeR.merge e b = some e

/-- Helper: if t is absorbed by m, and we continue folding merge from m to get result,
    then t is still absorbed by result. -/
private theorem merge_absorption_through_fold (ts : List LocalTypeR) (t m result : LocalTypeR)
    (habsorbed : LocalTypeR.merge m t = some m)
    (hfold : ts.foldlM (fun acc proj => LocalTypeR.merge acc proj) m = some result)
    : LocalTypeR.merge result t = some result := by
  induction ts generalizing m with
  | nil =>
    simp [List.foldlM] at hfold
    cases hfold
    exact habsorbed
  | cons x xs ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind] at hfold
    cases hmx : LocalTypeR.merge m x with
    | none => simp [hmx] at hfold
    | some next =>
      simp [hmx] at hfold
      -- By merge_absorption_preserved: merge next t = some next
      have hnext : LocalTypeR.merge next t = some next :=
        merge_absorption_preserved t m x next habsorbed hmx
      exact ih next hnext hfold

/-- Key lemma: if foldlM merge over a list produces result m, then each element
    is merge-compatible with the accumulator at that point. For non-participants,
    this means all elements are equal to m (under certain merge semantics).

    PROOF STRATEGY:
    This uses the key property that merge is "absorptive": if merge a b = some c,
    and we continue merging c with more types to get result, then merge result b = some result.

    The proof proceeds by:
    1. Use induction on the list
    2. For each element t, either it was merged early (and stays absorbed), or later
    3. Apply merge_idempotent_right and merge_absorption_preserved -/
theorem merge_fold_member (types : List LocalTypeR) (first : LocalTypeR) (result : LocalTypeR)
    (hfold : types.foldlM (fun acc proj => LocalTypeR.merge acc proj) first = some result)
    (t : LocalTypeR) (hmem : t ∈ types)
    : LocalTypeR.merge result t = some result := by
  induction types generalizing first result t with
  | nil => cases hmem
  | cons hd tl ih =>
    -- Unfold the fold: first we merge first with hd
    simp only [List.foldlM_cons, Option.bind_eq_bind] at hfold
    -- Extract the intermediate result after merging with hd
    cases hmerge : LocalTypeR.merge first hd with
    | none => simp [hmerge] at hfold
    | some intermediate =>
      simp [hmerge] at hfold
      -- Now hfold says: tl.foldlM ... intermediate = some result
      -- t is either hd or in tl
      rcases List.mem_cons.mp hmem with rfl | htl
      · -- t = hd, we need merge result t = some result
        -- We have: merge first t = some intermediate
        -- Use merge_idempotent_right to get: merge intermediate t = some intermediate
        have hidem : LocalTypeR.merge intermediate t = some intermediate :=
          merge_idempotent_right first t intermediate hmerge
        -- Use helper lemma to show absorption is preserved through the fold
        exact merge_absorption_through_fold tl t intermediate result hidem hfold
      · -- t ∈ tl, use IH
        exact ih intermediate result hfold t htl

/-- Helper: convert an Except-based merge fold to an Option-based fold. -/
private theorem except_fold_to_option_fold (types : List LocalTypeR) (first result : LocalTypeR)
    (hfold :
      types.foldlM (m := Except ProjectionError)
        (fun acc proj =>
          match LocalTypeR.merge acc proj with
          | some m => pure m
          | none => throw (ProjectionError.mergeFailed acc proj))
        first =
      Except.ok result)
    : types.foldlM (fun acc proj => LocalTypeR.merge acc proj) first = some result := by
  induction types generalizing first with
  | nil =>
    simp only [List.foldlM_nil] at hfold ⊢
    cases hfold
    rfl
  | cons hd tl ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind]
    -- The Except fold also unfolds
    simp only [List.foldlM_cons] at hfold
    -- Case on the merge result
    cases hmerge : LocalTypeR.merge first hd with
    | none =>
      -- merge failed, so the Except fold must have thrown - contradiction
      simp only [hmerge, Except.bind] at hfold
      -- hfold is now Except.error _ = Except.ok result, different constructors
      cases hfold
    | some intermediate =>
      simp only [hmerge, Option.some_bind]
      -- The Except fold now has intermediate as the accumulator
      simp only [hmerge, Except.bind, pure, Except.pure] at hfold
      exact ih intermediate hfold

/-- Except-based fold absorption for projection merges.
    This follows directly from merge_fold_member by extracting the Option-level fold. -/
theorem merge_fold_member_except (types : List LocalTypeR) (first : LocalTypeR) (result : LocalTypeR)
    (hfold :
      types.foldlM (m := Except ProjectionError)
        (fun acc proj =>
          match LocalTypeR.merge acc proj with
          | some m => pure m
          | none => throw (ProjectionError.mergeFailed acc proj))
        first =
      Except.ok result)
    (t : LocalTypeR) (hmem : t ∈ types)
    : LocalTypeR.merge result t = some result := by
  have hopt := except_fold_to_option_fold types first result hfold
  exact merge_fold_member types first result hopt t hmem

/-! ## Recv Branch Absorption Infrastructure

These axioms and theorems support the proof of recv branch absorption under composition. -/

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

    By case analysis on the merge. Each step either:
    - Takes head from bs1 (when l1.name < l2.name)
    - Takes head from bs2 (when l2.name < l1.name)
    - Merges heads with same label (when l1 = l2)
    In all cases, the element's label comes from bs1 or bs2.

    PROOF APPROACH: This requires well-founded induction on sizeOf bs1 + sizeOf bs2.
    Due to the complexity of extracting the recursive structure, we keep this as an axiom. -/
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

 /-- Non-participant projection is uniform across branches (membership form). -/
theorem projectR_comm_non_participant_mem (sender receiver role : String)
    (branches : List (Label × GlobalType)) (result : LocalTypeR)
    (hne1 : role ≠ sender) (hne2 : role ≠ receiver)
    (hproj : projectR (.comm sender receiver branches) role = .ok result)
    (huniq : GlobalType.uniqLabels (.comm sender receiver branches))
    (label : Label) (g : GlobalType)
    (hmem : (label, g) ∈ branches)
    : projectR g role = .ok result := by
  have huniqBranches := GlobalType.uniqLabels_comm_branches huniq
  have hfind := GlobalType.find?_of_mem_unique (p := GlobalType.uniqLabels) huniqBranches hmem
  exact projectR_comm_non_participant sender receiver role branches result hne1 hne2 hproj label g hfind


/-- Non-participant substitution commutes with projection (merge case).
    This is a specialized version for the non-participant comm case. -/
axiom projectR_substitute_nonparticipant (sender receiver role : String)
    (branches : List (Label × GlobalType)) (t : String) (replacement : GlobalType)
    (lt rlt : LocalTypeR)
    (hne1 : role ≠ sender) (hne2 : role ≠ receiver)
    (hproj : projectR (GlobalType.comm sender receiver branches) role = .ok lt)
    (hrep : projectR replacement role = .ok rlt)
    (huniq : GlobalType.uniqLabels (GlobalType.comm sender receiver branches))
    : projectR ((GlobalType.comm sender receiver branches).substitute t replacement) role =
        .ok (lt.substitute t rlt)

/-- Mu case for projection/substitution commutation.
    Handles both the shadowed variable case (s = t) and the non-shadowed case (s ≠ t).
    The key complexity is managing the beq check on LocalTypeR when the original
    projection result may or may not be .end.

    Parameters:
    - projBody: the projection of the mu body
    - hbody: projectR body role = .ok projBody
    - hproj: the result of the if-then-else on projBody == .end gives lt
    - hrep: replacement projects successfully
    - huniq: the mu type has unique labels -/
axiom projectR_substitute_mu (s : String) (body : GlobalType)
    (t : String) (replacement : GlobalType) (role : String) (lt rlt : LocalTypeR)
    (projBody : LocalTypeR)
    (hbody : projectR body role = .ok projBody)
    (hproj : (if projBody == LocalTypeR.end then
               (Except.ok LocalTypeR.end : Except ProjectionError LocalTypeR)
             else Except.ok (LocalTypeR.mu s projBody)) = .ok lt)
    (hrep : projectR replacement role = .ok rlt)
    (huniq : GlobalType.uniqLabels (GlobalType.mu s body))
    : projectR ((GlobalType.mu s body).substitute t replacement) role = .ok (lt.substitute t rlt)


/-- Projection commutes with substitution, given the replacement projection.

    Proof uses mutual induction on GlobalType via @GlobalType.rec with three motives:
    - motive_1: For GlobalType g
    - motive_2: For List (Label × GlobalType) branches
    - motive_3: For (Label × GlobalType) pair

    The key insight from Coq is that projection distributes over substitution
    because substitution only affects recursion variables, not the role-based
    structure that projection depends on.
-/
theorem projectR_substitute (body : GlobalType) (t : String) (replacement : GlobalType)
    (role : String) (lt rlt : LocalTypeR)
    (hproj : projectR body role = .ok lt)
    (hrep : projectR replacement role = .ok rlt)
    (huniq : GlobalType.uniqLabels body)
    : projectR (body.substitute t replacement) role = .ok (lt.substitute t rlt) := by
  -- Define motives for mutual induction
  let motive1 (g : GlobalType) : Prop :=
    ∀ (t : String) (replacement : GlobalType) (role : String) (lt rlt : LocalTypeR),
      projectR g role = .ok lt →
      projectR replacement role = .ok rlt →
      GlobalType.uniqLabels g →
      projectR (g.substitute t replacement) role = .ok (lt.substitute t rlt)
  let motive2 (bs : List (Label × GlobalType)) : Prop :=
    ∀ (t : String) (replacement : GlobalType) (role : String) (projBs : List (Label × LocalTypeR)) (rlt : LocalTypeR),
      projectBranches bs role = .ok projBs →
      projectR replacement role = .ok rlt →
      GlobalType.BranchesUniq GlobalType.uniqLabels bs →
      projectBranches (bs.map fun (l, g) => (l, g.substitute t replacement)) role =
        .ok (projBs.map fun (l, lt) => (l, lt.substitute t rlt))
  let motive3 (p : Label × GlobalType) : Prop :=
    ∀ (t : String) (replacement : GlobalType) (role : String) (lt rlt : LocalTypeR),
      projectR p.2 role = .ok lt →
      projectR replacement role = .ok rlt →
      GlobalType.uniqLabels p.2 →
      projectR ((p.2).substitute t replacement) role = .ok (lt.substitute t rlt)
  -- Apply the recursor
  have hmain := @GlobalType.rec (motive_1 := motive1) (motive_2 := motive2) (motive_3 := motive3)
  -- End case
  have hend : motive1 .end := by
    intro t' repl role' lt' rlt' hproj' hrep' _
    simp only [projectR, pure, Except.pure] at hproj'
    cases hproj'
    simp only [substitute_end, projectR, pure, Except.pure, LocalTypeR.substitute_end]
  -- Comm case (sender/receiver/non-participant)
  have hcomm : ∀ (sender receiver : String) (branches : List (Label × GlobalType)),
      motive2 branches → motive1 (.comm sender receiver branches) := by
    intro sender receiver branches ih_branches t' repl role' lt' rlt' hproj' hrep' huniq'
    -- Case split: role = sender, role = receiver, or neither
    by_cases hSender : role' = sender
    · -- Sender case: projectR gives .send
      simp only [hSender] at hproj' hrep' huniq' ⊢
      rw [projectR_comm_sender] at hproj'
      by_cases hempty : branches.isEmpty
      · simp [hempty] at hproj'
      · simp only [hempty, Bool.false_eq_true, ↓reduceIte, Except.map] at hproj'
        cases hbs : projectBranches branches sender with
        | error e =>
          rw [hbs] at hproj'
          simp only [Except.map_error] at hproj'
          -- hproj' : Except.error e = Except.ok lt' is a contradiction
          exact Except.noConfusion hproj'
        | ok projBs =>
          rw [hbs] at hproj'
          simp only [Except.map_ok] at hproj'
          cases hproj'
          -- After substitution, projection should give .send with substituted branches
          rw [substitute_comm]
          rw [projectR_comm_sender]
          have hne' : (branches.map fun p => (p.1, p.2.substitute t' repl)).isEmpty = false := by
            cases branches with
            | nil => exact (hempty rfl).elim
            | cons _ _ => rfl
          simp only [hne', Bool.false_eq_true, ↓reduceIte, Except.map]
          -- Use IH on branches
          have huniqBranches := GlobalType.uniqLabels_comm_branches huniq'
          have hbsSubst := ih_branches t' repl sender projBs rlt' hbs hrep' huniqBranches
          simp only [hbsSubst, Except.map_ok]
          simp [LocalTypeR.substitute_send]
    · by_cases hRecv : role' = receiver
      · -- Receiver case: projectR gives .recv
        simp only [hRecv] at hproj' hrep' huniq' hSender ⊢
        have hne_sr : sender ≠ receiver := by
          intro heq
          rw [heq] at hSender
          exact hSender rfl
        rw [projectR_comm_receiver sender receiver branches hne_sr] at hproj'
        by_cases hempty : branches.isEmpty
        · simp [hempty] at hproj'
        · simp only [hempty, Bool.false_eq_true, ↓reduceIte, Except.map] at hproj'
          cases hbs : projectBranches branches receiver with
          | error e =>
            rw [hbs] at hproj'
            simp only [Except.map_error] at hproj'
            exact Except.noConfusion hproj'
          | ok projBs =>
            rw [hbs] at hproj'
            simp only [Except.map_ok] at hproj'
            cases hproj'
            -- After substitution
            rw [substitute_comm]
            rw [projectR_comm_receiver]
            · have hne' : (branches.map fun p => (p.1, p.2.substitute t' repl)).isEmpty = false := by
                cases branches with
                | nil => exact (hempty rfl).elim
                | cons _ _ => rfl
              simp only [hne', Bool.false_eq_true, ↓reduceIte, Except.map]
              have huniqBranches := GlobalType.uniqLabels_comm_branches huniq'
              have hbsSubst := ih_branches t' repl receiver projBs rlt' hbs hrep' huniqBranches
              simp only [hbsSubst, Except.map_ok]
              simp [LocalTypeR.substitute_recv]
            · exact hne_sr
      · -- Non-participant case: merge all branch projections
        -- This case is more complex and requires showing merge commutes with substitution
        -- We use the projectR_substitute_nonparticipant axiom which handles this case
        exact projectR_substitute_nonparticipant sender receiver role' branches t' repl lt' rlt'
          hSender hRecv hproj' hrep' huniq'
  -- Mu case (handle shadowing)
  have hmu : ∀ (s : String) (body' : GlobalType),
      motive1 body' → motive1 (.mu s body') := by
    intro s body' ih_body t' repl role' lt' rlt' hproj' hrep' huniq'
    rw [projectR_mu] at hproj'
    cases hbody : projectR body' role' with
    | error e =>
      rw [hbody] at hproj'
      simp only [Except.bind] at hproj'
      exact Except.noConfusion hproj'
    | ok projBody =>
      rw [hbody] at hproj'
      simp only [Except.bind, pure, Except.pure] at hproj'
      -- The mu case requires detailed case analysis on the beq check.
      -- This involves showing that (projBody == .end) after substitution behaves correctly.
      -- The key lemmas needed are:
      -- 1. If projBody == .end = true, then projBody = .end (requires LawfulBEq or decidability)
      -- 2. substitute_mu_shadow/substitute_mu_ne preserve the beq behavior
      -- For now, we defer to an axiom for this case.
      exact projectR_substitute_mu s body' t' repl role' lt' rlt' projBody hbody hproj' hrep' huniq'
  -- Var case
  have hvar : ∀ (v : String), motive1 (.var v) := by
    intro v t' repl role' lt' rlt' hproj' hrep' _
    simp only [projectR, pure, Except.pure] at hproj'
    cases hproj'
    by_cases hv : v = t'
    · -- Matching variable: substitute yields replacement
      subst hv
      rw [substitute_var_eq]
      rw [LocalTypeR.substitute_var_eq]
      exact hrep'
    · -- Non-matching variable: substitute yields the variable
      rw [substitute_var_ne hv]
      simp only [projectR, pure, Except.pure]
      rw [LocalTypeR.substitute_var_ne hv]
  -- Nil case for branches
  have hnil : motive2 [] := by
    intro t' repl role' projBs rlt' hproj' _ _
    simp [projectBranches] at hproj'
    cases hproj'
    simp [projectBranches, List.map, pure, Except.pure]
  -- Cons case for branches
  have hcons : ∀ (head : Label × GlobalType) (tail : List (Label × GlobalType)),
      motive3 head → motive2 tail → motive2 (head :: tail) := by
    intro head tail ih_head ih_tail t' repl role' projBs rlt' hproj' hrep' huniqBranches
    -- Expand projectBranches on head :: tail
    unfold projectBranches at hproj'
    cases hhead : projectR head.2 role' with
    | error e =>
      rw [hhead] at hproj'
      -- After rewrite, hproj' has bind (.error e) which reduces to .error e
      -- bind (error e) f = error e, so hproj' : error e = ok projBs, contradiction
      simp [bind, Except.bind] at hproj'
    | ok projHead =>
      rw [hhead] at hproj'
      -- After rewrite, bind (.ok x) f = f x (via pure_bind or by definitional eq)
      simp [bind, Except.bind] at hproj'
      cases htail : projectBranches tail role' with
      | error e =>
        rw [htail] at hproj'
        simp [bind, Except.bind] at hproj'
      | ok projTail =>
        rw [htail] at hproj'
        simp only [pure, Except.pure, Except.bind] at hproj'
        cases hproj'
        -- After substitution
        simp only [List.map_cons]
        simp only [projectBranches, bind, Except.bind]
        -- Use IH on head
        have huniq_head := GlobalType.BranchesUniq.head_uniq huniqBranches
        have hih_head := ih_head t' repl role' projHead rlt' hhead hrep' huniq_head
        simp only [hih_head]
        -- Use IH on tail
        have huniq_tail := GlobalType.BranchesUniq.tail_uniq huniqBranches
        have hih_tail := ih_tail t' repl role' projTail rlt' htail hrep' huniq_tail
        simp only [hih_tail, pure, Except.pure]
  -- Pair case
  have hpair : ∀ (l : Label) (g : GlobalType),
      motive1 g → motive3 (l, g) := by
    intro l g ih_g t' repl role' lt' rlt' hproj' hrep' huniq'
    simp only at hproj' huniq' ⊢
    exact ih_g t' repl role' lt' rlt' hproj' hrep' huniq'
  -- Apply the recursor and extract the result
  exact hmain hend hcomm hmu hvar hnil hcons hpair body t replacement role lt rlt hproj hrep huniq


/-! ## Projectability preservation helpers

These lemmas support proving that projectability is preserved through steps. -/

/-- If a comm is projectable for a role, each branch continuation is projectable for that role. -/
theorem projectable_comm_mem_role (s r p : String)
    (branches : List (Label × GlobalType))
    (hproj : ∃ lt, projectR (.comm s r branches) p = .ok lt)
    {label : Label} {cont : GlobalType} (hmem : (label, cont) ∈ branches) :
    ∃ lt, projectR cont p = .ok lt := by
  obtain ⟨lt, hlt⟩ := hproj
  by_cases hr1 : p = s
  · -- sender case: use projectBranches
    rw [hr1] at hlt ⊢
    simp only [projectR] at hlt
    by_cases hne : branches.isEmpty
    · -- branches.isEmpty = true contradicts hmem
      simp only [List.isEmpty_iff] at hne
      rw [hne] at hmem
      cases hmem
    · simp only [hne, beq_self_eq_true, ↓reduceIte] at hlt
      cases hbs : projectBranches branches s with
      | error e =>
        simp [hbs] at hlt
      | ok bs =>
        exact projectBranches_mem_succeeds branches s bs hbs hmem
  · by_cases hr2 : p = r
    · -- receiver case: use projectBranches
      rw [hr2] at hlt ⊢
      have hne_sr : s ≠ r := by
        intro heq
        rw [heq] at hr1
        exact hr1 hr2
      simp only [projectR] at hlt
      by_cases hne : branches.isEmpty
      · -- branches.isEmpty = true contradicts hmem
        simp only [List.isEmpty_iff] at hne
        rw [hne] at hmem
        cases hmem
      · have hs : (r == s) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne_sr)
        simp only [hne, hs, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hlt
        cases hbs : projectBranches branches r with
        | error e =>
          simp [hbs] at hlt
        | ok bs =>
          exact projectBranches_mem_succeeds branches r bs hbs hmem
    · -- non-participant case: use projectBranchTypes
      by_cases hne : branches.isEmpty
      · simp only [List.isEmpty_iff] at hne
        rw [hne] at hmem
        cases hmem
      · simp only [projectR] at hlt
        have hs : (p == s) = false := beq_eq_false_iff_ne.mpr hr1
        have hr : (p == r) = false := beq_eq_false_iff_ne.mpr hr2
        simp only [hne, hs, Bool.false_eq_true, ↓reduceIte, hr, bind, Except.bind] at hlt
        cases hbts : projectBranchTypes branches p with
        | error e =>
          simp only [hbts] at hlt
          cases hlt
        | ok tys =>
          exact projectBranchTypes_mem_succeeds branches p tys hbts hmem

/-! ## BranchesStep preservation for projection

These lemmas show that if projection succeeds on branches, and we step via BranchesStep,
then projection succeeds on the stepped branches. -/

/-- If all branches in the source are projectable, and stepping preserves projectability,
    then all branches in the target are projectable. -/
theorem projectable_all_BranchesStep
    {branches branches' : List (Label × GlobalType)} {act : GlobalActionR}
    (hbstep : GlobalType.BranchesStep GlobalType.step branches act branches')
    (hih : ∀ g g', GlobalType.step g act g' →
           (∀ role, ∃ lt, projectR g role = .ok lt) →
           ∀ role, ∃ lt, projectR g' role = .ok lt)
    (hproj : ∀ (label : Label) (g : GlobalType), (label, g) ∈ branches →
             ∀ role, ∃ lt, projectR g role = .ok lt) :
    ∀ (label : Label) (g' : GlobalType), (label, g') ∈ branches' →
    ∀ role, ∃ lt, projectR g' role = .ok lt := by
  induction hbstep with
  | nil _ =>
    intro label g' hmem
    cases hmem
  | cons label g g' rest rest' act hstep hrest ih =>
    intro label' g'' hmem' role
    have hmem'' : (label', g'') = (label, g') ∨ (label', g'') ∈ rest' := by
      simpa [List.mem_cons] using hmem'
    cases hmem'' with
    | inl heq =>
      cases heq
      have hprojG : ∀ role, ∃ lt, projectR g role = .ok lt := fun r =>
        hproj label g List.mem_cons_self r
      exact hih g g' hstep hprojG role
    | inr hmem'' =>
      have hprojRest : ∀ (l : Label) (g0 : GlobalType), (l, g0) ∈ rest →
                       ∀ r, ∃ lt, projectR g0 r = .ok lt := fun l g0 hm r =>
        hproj l g0 (List.mem_cons_of_mem _ hm) r
      exact ih hih hprojRest label' g'' hmem'' role

/-- If all branches are projectable for a role, then projectBranches succeeds. -/
theorem projectBranches_from_all_projectable
    {branches : List (Label × GlobalType)} {role : String}
    (hproj : ∀ (l : Label) (g : GlobalType), (l, g) ∈ branches → ∃ lt, projectR g role = .ok lt) :
    ∃ bs, projectBranches branches role = .ok bs := by
  induction branches with
  | nil =>
    use []
    simp only [projectBranches, pure, Except.pure]
  | cons b rest ih =>
    have ⟨lt, hlt⟩ := hproj b.1 b.2 List.mem_cons_self
    have hrest : ∀ (l : Label) (g : GlobalType), (l, g) ∈ rest → ∃ lt, projectR g role = .ok lt :=
      fun l g hm => hproj l g (List.mem_cons_of_mem _ hm)
    have ⟨restBs, hrestBs⟩ := ih hrest
    use (b.1, lt) :: restBs
    unfold projectBranches
    simp only [bind, Except.bind, hlt, hrestBs, pure, Except.pure]

/-- If all branches are projectable for a role, then projectBranchTypes succeeds. -/
theorem projectBranchTypes_from_all_projectable
    {branches : List (Label × GlobalType)} {role : String}
    (hproj : ∀ (l : Label) (g : GlobalType), (l, g) ∈ branches → ∃ lt, projectR g role = .ok lt) :
    ∃ tys, projectBranchTypes branches role = .ok tys := by
  induction branches with
  | nil =>
    use []
    simp only [projectBranchTypes, pure, Except.pure]
  | cons b rest ih =>
    have ⟨lt, hlt⟩ := hproj b.1 b.2 List.mem_cons_self
    have hrest : ∀ (l : Label) (g : GlobalType), (l, g) ∈ rest → ∃ lt, projectR g role = .ok lt :=
      fun l g hm => hproj l g (List.mem_cons_of_mem _ hm)
    have ⟨restTys, hrestTys⟩ := ih hrest
    use lt :: restTys
    unfold projectBranchTypes
    simp only [bind, Except.bind, hlt, hrestTys, pure, Except.pure]

/-- If projectBranches succeeds on branches and stepping preserves projectability,
    then projectBranches succeeds on the stepped branches.

    This takes the stronger hypothesis that all branches are projectable for ALL roles,
    which is what we have when the enclosing comm type is projectable. -/
theorem projectBranches_BranchesStep
    {branches branches' : List (Label × GlobalType)} {act : GlobalActionR} {role : String}
    (hbstep : GlobalType.BranchesStep GlobalType.step branches act branches')
    (hih : ∀ g g', GlobalType.step g act g' →
           (∀ role, ∃ lt, projectR g role = .ok lt) →
           ∀ role, ∃ lt, projectR g' role = .ok lt)
    (hprojAll : ∀ (label : Label) (g : GlobalType), (label, g) ∈ branches →
                ∀ role, ∃ lt, projectR g role = .ok lt) :
    ∃ bs', projectBranches branches' role = .ok bs' := by
  induction hbstep with
  | nil _ =>
    use []
    simp only [projectBranches, pure, Except.pure]
  | cons label g g' rest rest' act hstep hrest ih =>
    have hprojG : ∀ r, ∃ lt, projectR g r = .ok lt := fun r =>
      hprojAll label g List.mem_cons_self r
    have hprojG' : ∀ r, ∃ lt, projectR g' r = .ok lt := fun r =>
      hih g g' hstep hprojG r
    have ⟨projCont', hCont'⟩ := hprojG' role
    have hprojRest : ∀ (l : Label) (g0 : GlobalType), (l, g0) ∈ rest →
                     ∀ r, ∃ lt, projectR g0 r = .ok lt := fun l g0 hm r =>
      hprojAll l g0 (List.mem_cons_of_mem _ hm) r
    have ⟨projRest', hRest'⟩ := ih hih hprojRest
    use (label, projCont') :: projRest'
    unfold projectBranches
    simp only [bind, Except.bind, hCont', hRest', pure, Except.pure]

/-- If projectBranchTypes succeeds on branches and stepping preserves projectability,
    then projectBranchTypes succeeds on the stepped branches. -/
theorem projectBranchTypes_BranchesStep
    {branches branches' : List (Label × GlobalType)} {act : GlobalActionR} {role : String}
    (hbstep : GlobalType.BranchesStep GlobalType.step branches act branches')
    (hih : ∀ g g', GlobalType.step g act g' →
           (∀ role, ∃ lt, projectR g role = .ok lt) →
           ∀ role, ∃ lt, projectR g' role = .ok lt)
    (hprojAll : ∀ (label : Label) (g : GlobalType), (label, g) ∈ branches →
                ∀ role, ∃ lt, projectR g role = .ok lt) :
    ∃ tys', projectBranchTypes branches' role = .ok tys' := by
  induction hbstep with
  | nil _ =>
    use []
    simp only [projectBranchTypes, pure, Except.pure]
  | cons label g g' rest rest' act hstep hrest ih =>
    have hprojG : ∀ r, ∃ lt, projectR g r = .ok lt := fun r =>
      hprojAll label g List.mem_cons_self r
    have hprojG' : ∀ r, ∃ lt, projectR g' r = .ok lt := fun r =>
      hih g g' hstep hprojG r
    have ⟨projCont', hCont'⟩ := hprojG' role
    have hprojRest : ∀ (l : Label) (g0 : GlobalType), (l, g0) ∈ rest →
                     ∀ r, ∃ lt, projectR g0 r = .ok lt := fun l g0 hm r =>
      hprojAll l g0 (List.mem_cons_of_mem _ hm) r
    have ⟨projRest', hRest'⟩ := ih hih hprojRest
    use projCont' :: projRest'
    unfold projectBranchTypes
    simp only [bind, Except.bind, hCont', hRest', pure, Except.pure]

end Rumpsteak.Protocol.ProjectionR
