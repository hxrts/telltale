import Mathlib.Order.FixedPoints
import SessionCoTypes.CoinductiveRel
import Choreography.Projection.Trans.Core
import SessionTypes.Participation


/-
The Problem. Define a coinductive projection relation CProject that captures when a global
type g projects to a local type e for a given role. The challenge is twofold:
1. Projection is inherently coinductive: recursive types unfold infinitely, so we need
   a greatest fixed point construction rather than inductive proof
2. We need both a boolean checker (projectb) for computation and a coinductive relation
   (CProject) for reasoning, and these must be sound and complete with respect to each other

The boolean checker faces termination challenges with recursion. The coinductive relation
provides the logical specification but requires careful setup of the generator function
(CProjectF) and coinduction principles.

For non-participants in a communication, all branches must project to the same local type,
which requires universal quantification over branches - a non-trivial property to verify.

Solution Structure. The module is organized into six main sections:
1. Boolean checker: projectb and helper functions with termination proofs
2. Coinductive relation: CProjectF generator and CProject as greatest fixed point
3. Constructor lemmas: convenient ways to build CProject proofs
4. Reflection lemmas: connecting boolean tests to coinductive relation
5. Soundness: projectb true implies CProject
6. Completeness: CProject implies projectb true
-/

/-! # Choreography.Projection.Projectb

Boolean checker for V2 projection (`projectb`).

## Expose

The following definitions form the semantic interface for proofs:

- `projectb`: boolean projection checker
- `projectbBranches`: branch-wise projection for participants
- `projectbAllBranches`: single candidate check for non-participants
- `CProjectF`: one-step generator for coinductive projection
- `CProject`: coinductive projection relation (greatest fixed point of CProjectF)
- `CProject_coind`: coinduction principle for CProject
- `BranchesProjRel`: branch-wise projection for send/recv
- `AllBranchesProj`: all branches project to same candidate
- `projectb_end_end`: reflection lemma for end-end
- `projectb_var_var`: reflection lemma for var-var
- `projectb_mu_mu`: reflection lemma for mu-mu
- `projectb_comm_other`: reflection lemma for non-participant
-/

namespace Choreography.Projection.Projectb

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel
open Choreography.Projection.Trans (lcontractive)

/-! ## Size-Of Lemmas for Termination -/

private theorem sizeOf_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf (x :: l) = 1 + sizeOf x + sizeOf l := by
  simp [sizeOf, List._sizeOf_1]

private theorem sizeOf_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp [sizeOf, Prod._sizeOf_1]

private theorem sizeOf_snd_lt_prod {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β) :
    sizeOf b < sizeOf (a, b) := by
  simp only [sizeOf, Prod._sizeOf_1]
  omega

private theorem sizeOf_head_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf x < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_tail_lt_cons {α : Type} [SizeOf α] (x : α) (l : List α) :
    sizeOf l < sizeOf (x :: l) := by
  simp only [sizeOf, List._sizeOf_1]
  omega

private theorem sizeOf_head_snd_lt_cons (pair : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf pair.2 < sizeOf (pair :: rest) := by
  have h1 : sizeOf pair.2 < sizeOf pair := sizeOf_snd_lt_prod pair.1 pair.2
  have h2 : sizeOf pair < sizeOf (pair :: rest) := sizeOf_head_lt_cons pair rest
  exact Nat.lt_trans h1 h2

private theorem sizeOf_cont_lt_branch_cons (label : Label) (cont : GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf cont < sizeOf ((label, cont) :: rest) := by
  have h : sizeOf cont < sizeOf (label, cont) := sizeOf_snd_lt_prod label cont
  have h2 : sizeOf (label, cont) < sizeOf ((label, cont) :: rest) :=
    sizeOf_head_lt_cons (label, cont) rest
  exact Nat.lt_trans h h2

private theorem sizeOf_rest_lt_branch_cons (label : Label) (cont : GlobalType)
    (rest : List (Label × GlobalType)) :
    sizeOf rest < sizeOf ((label, cont) :: rest) :=
  sizeOf_tail_lt_cons (label, cont) rest

theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simp only [Nat.one_add]
    exact Nat.succ_pos (sizeOf t)
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simp only [sizeOf, GlobalType._sizeOf_1]
  omega

/-! ## Size-Of Lemmas for Branch/Comm Cases -/

private theorem sizeOf_bs_lt_comm (sender receiver : String) (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

private theorem sizeOf_elem_snd_lt_list {α β : Type _} [SizeOf α] [SizeOf β]
    (xs : List (α × β)) (x : α × β) (h : x ∈ xs) :
    sizeOf x.2 < sizeOf xs := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
      cases h with
      | head => simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]; omega
      | tail _ hmem => have := ih hmem; simp only [sizeOf, List._sizeOf_1] at *; omega

theorem sizeOf_elem_snd_lt_comm (sender receiver : String)
    (gbs : List (Label × GlobalType)) (gb : Label × GlobalType) (h : gb ∈ gbs) :
    sizeOf gb.2 < sizeOf (GlobalType.comm sender receiver gbs) := by
  have h1 := sizeOf_elem_snd_lt_list gbs gb h
  have h2 := sizeOf_bs_lt_comm sender receiver gbs
  omega

/-! ## Boolean Projection Checker -/

mutual
  /-! ## Boolean Checker: Global Type Case -/

  /- Boolean Projection Checker: Global Type Case. -/

  /-- Boolean projection checker (`projectb`). -/
  def projectb : GlobalType → String → LocalTypeR → Bool
    | .end, _, cand => -- Dispatch by global head; each case validates candidate shape and recurses.
        match cand with | .end => true | _ => false
    | .var t, _, cand =>
        match cand with | .var t' => t == t' | _ => false
    | .mu t body, role, cand =>
        match cand with
        | .mu t' candBody =>
            if t == t' then if candBody.isGuarded t' then projectb body role candBody else false else false
        | .end =>
            let candBody := Trans.trans body role
            if candBody.isGuarded t then false else projectb body role candBody
        | _ => false
    | .comm sender receiver branches, role, cand =>
        if role == sender then
          match cand with
          | .send partner cands =>
              if partner == receiver then projectbBranches branches role cands else false
          | _ => false
        else if role == receiver then
          match cand with
          | .recv partner cands =>
              if partner == sender then projectbBranches branches role cands else false
          | _ => false
        else
          projectbAllBranches branches role cand
    /-! ## Boolean Checker: Delegation Case -/
    | .delegate p q sid r cont, role, cand =>
        if role == p then
          -- delegator: must be send to q
          match cand with
          | .send partner [(lbl, vt, contCand)] =>
              if partner == q then
                if lbl == ⟨"_delegate", .unit⟩ then
                  if vt == some (.chan sid r) then projectb cont role contCand else false
                else
                  false
              else
                false
          | _ => false
        else if role == q then
          -- delegatee: must be recv from p
          match cand with
          | .recv partner [(lbl, vt, contCand)] =>
              if partner == p then
                if lbl == ⟨"_delegate", .unit⟩ then
                  if vt == some (.chan sid r) then projectb cont role contCand else false
                else
                  false
              else
                false
          | _ => false
        else
          -- non-participant: follows continuation
          projectb cont role cand
  termination_by g _ _ => sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _
      | simp only [sizeOf, GlobalType._sizeOf_1]; omega

  /-! ## Boolean Checker: Participant Branches -/

  /- Boolean Projection Checker: Branch List Case. -/

  /-- Check branch-wise projection for participant roles. -/
  def projectbBranches :
      List (Label × GlobalType) → String → List BranchR → Bool
    | [], _, [] => true
    | (label, cont) :: rest, role, (label', vt, cand) :: rest' =>
        if label == label' then
          if vt == none then
            projectb cont role cand && projectbBranches rest role rest'
          else
            false
        else
          false
    | _, _, _ => false
  termination_by bs _ _ => sizeOf bs
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_branch_cons _ _ _
      | exact sizeOf_rest_lt_branch_cons _ _ _

  /-! ## Boolean Checker: Non-Participant Branches -/

  /- Boolean Projection Checker: Non-Participant Case. -/

  /-- Check a single candidate against all branches for non-participants. -/
  def projectbAllBranches :
      List (Label × GlobalType) → String → LocalTypeR → Bool
    | [], _, _ => true
    | (_, cont) :: rest, role, cand =>
        projectb cont role cand && projectbAllBranches rest role cand
  termination_by bs _ _ => sizeOf bs
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_branch_cons _ _ _
      | exact sizeOf_rest_lt_branch_cons _ _ _
end

end Choreography.Projection.Projectb
