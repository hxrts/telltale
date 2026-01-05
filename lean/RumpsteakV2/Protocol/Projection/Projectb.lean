import Mathlib.Order.FixedPoints
import RumpsteakV2.Protocol.Projection.Trans

/-! # RumpsteakV2.Protocol.Projection.Projectb

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

namespace RumpsteakV2.Protocol.Projection.Projectb

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans (lcontractive)

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

private theorem sizeOf_body_lt_mu (t : String) (body : GlobalType) :
    sizeOf body < sizeOf (GlobalType.mu t body) := by
  have hk : 0 < 1 + sizeOf t := by
    simp only [Nat.one_add]
    exact Nat.succ_pos (sizeOf t)
  have h : sizeOf body < (1 + sizeOf t) + sizeOf body :=
    Nat.lt_add_of_pos_left (n := sizeOf body) (k := 1 + sizeOf t) hk
  simp only [sizeOf, GlobalType._sizeOf_1]
  omega

private theorem sizeOf_bs_lt_comm (sender receiver : String) (bs : List (Label × GlobalType)) :
    sizeOf bs < sizeOf (GlobalType.comm sender receiver bs) := by
  simp only [GlobalType.comm.sizeOf_spec]
  have h : 0 < 1 + sizeOf sender + sizeOf receiver := by omega
  omega

mutual
  /-- Boolean projection checker (`projectb`). -/
  def projectb : GlobalType → String → LocalTypeR → Bool
    | .end, _, cand =>
        match cand with
        | .end => true
        | _ => false
    | .var t, _, cand =>
        match cand with
        | .var t' => t == t'
        | _ => false
    | .mu t body, role, cand =>
        match cand with
        | .mu t' candBody =>
            if t == t' then
              if lcontractive body then
                projectb body role candBody
              else
                false
            else
              false
        | _ => false
    | .comm sender receiver branches, role, cand =>
        if role == sender then
          match cand with
          | .send partner cands =>
              if partner == receiver then
                projectbBranches branches role cands
              else
                false
          | _ => false
        else if role == receiver then
          match cand with
          | .recv partner cands =>
              if partner == sender then
                projectbBranches branches role cands
              else
                false
          | _ => false
        else
          projectbAllBranches branches role cand
  termination_by g _ _ => sizeOf g
  decreasing_by
    all_goals
      first
      | exact sizeOf_body_lt_mu _ _
      | exact sizeOf_bs_lt_comm _ _ _

  /-- Check branch-wise projection for participant roles. -/
  def projectbBranches :
      List (Label × GlobalType) → String → List (Label × LocalTypeR) → Bool
    | [], _, [] => true
    | (label, cont) :: rest, role, (label', cand) :: rest' =>
        if label == label' then
          projectb cont role cand && projectbBranches rest role rest'
        else
          false
    | _, _, _ => false
  termination_by bs _ _ => sizeOf bs
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_branch_cons _ _ _
      | exact sizeOf_rest_lt_branch_cons _ _ _

  /-- Check a single candidate against all branches for non-participants. -/
  def projectbAllBranches :
      List (Label × GlobalType) → String → LocalTypeR → Bool
    | [], _, _ => true
    | (label, cont) :: rest, role, cand =>
        projectb cont role cand && projectbAllBranches rest role cand
  termination_by bs _ _ => sizeOf bs
  decreasing_by
    all_goals
      first
      | exact sizeOf_cont_lt_branch_cons _ _ _
      | exact sizeOf_rest_lt_branch_cons _ _ _
end

/-! ## CProject Coinductive Relation

CProject is defined as the greatest fixed point of CProjectF, which captures
one step of the projection relation. This is analogous to how EQ2 is defined
for local type equality. -/

/-- Ternary relation for projection. -/
abbrev ProjRel := GlobalType → String → LocalTypeR → Prop

/-- Branch-wise projection relation for send/recv. -/
def BranchesProjRel (R : ProjRel)
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List (Label × LocalTypeR)) : Prop :=
  List.Forall₂ (fun gb lb => gb.1 = lb.1 ∧ R gb.2 role lb.2) gbs lbs

/-- All branches project to the same candidate (for non-participants). -/
def AllBranchesProj (R : ProjRel)
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR) : Prop :=
  ∀ gb ∈ gbs, R gb.2 role cand

/-- One-step generator for CProject.
    For comm nodes, we check role participation first to properly handle all cases. -/
def CProjectF (R : ProjRel) : ProjRel := fun g role cand =>
  match g, cand with
  | .end, .end => True
  | .var t, .var t' => t = t'
  | .mu t body, .mu t' candBody =>
      t = t' ∧ lcontractive body ∧ R body role candBody
  | .comm sender receiver gbs, cand =>
      if role = sender then
        match cand with
        | .send partner lbs => partner = receiver ∧ BranchesProjRel R gbs role lbs
        | _ => False
      else if role = receiver then
        match cand with
        | .recv partner lbs => partner = sender ∧ BranchesProjRel R gbs role lbs
        | _ => False
      else
        AllBranchesProj R gbs role cand
  | _, _ => False

private theorem BranchesProjRel_mono {R S : ProjRel}
    (h : ∀ g r c, R g r c → S g r c) :
    ∀ {gbs lbs role}, BranchesProjRel R gbs role lbs → BranchesProjRel S gbs role lbs := by
  intro gbs lbs role hrel
  induction hrel with
  | nil => exact List.Forall₂.nil
  | cons hpair _ ih =>
      exact List.Forall₂.cons ⟨hpair.1, h _ _ _ hpair.2⟩ ih

private theorem AllBranchesProj_mono {R S : ProjRel}
    (h : ∀ g r c, R g r c → S g r c) :
    ∀ {gbs role cand}, AllBranchesProj R gbs role cand → AllBranchesProj S gbs role cand := by
  intro gbs role cand hall gb hgb
  exact h _ _ _ (hall gb hgb)

private theorem CProjectF_mono : Monotone CProjectF := by
  intro R S h g role cand hrel
  cases g <;> cases cand <;> simp only [CProjectF] at hrel ⊢
  all_goals
    first
    | exact hrel                                                -- trivial cases
    | (obtain ⟨h1, h2, h3⟩ := hrel;                             -- mu case
       exact ⟨h1, h2, h _ _ _ h3⟩)
    | (-- comm cases with if-then-else structure
       split_ifs at hrel ⊢
       all_goals
         first
         | exact hrel
         | (obtain ⟨h1, h2⟩ := hrel; exact ⟨h1, BranchesProjRel_mono h h2⟩)
         | exact AllBranchesProj_mono h hrel)

/-- CProject as the greatest fixed point of CProjectF.
    Uses the pointwise complete lattice structure on ProjRel. -/
def CProject : ProjRel :=
  OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩

private theorem CProject_fixed : CProjectF CProject = CProject := by
  simpa [CProject] using (OrderHom.isFixedPt_gfp ⟨CProjectF, CProjectF_mono⟩)

/-- Coinduction principle for CProject: if R ⊆ CProjectF R, then R ⊆ CProject. -/
theorem CProject_coind {R : ProjRel} (h : ∀ g role cand, R g role cand → CProjectF R g role cand) :
    ∀ g role cand, R g role cand → CProject g role cand := by
  intro g role cand hr
  have hle : R ≤ CProjectF R := fun x y z hxyz => h x y z hxyz
  have hgfp : R ≤ CProject := OrderHom.le_gfp ⟨CProjectF, CProjectF_mono⟩ hle
  exact hgfp g role cand hr

/-- Destruct CProject: if CProject holds, then CProjectF CProject holds. -/
theorem CProject_destruct {g : GlobalType} {role : String} {cand : LocalTypeR}
    (h : CProject g role cand) : CProjectF CProject g role cand := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  exact Eq.mp (congrFun (congrFun (congrFun hfix.symm g) role) cand) h

/-! ## Constructor-style lemmas for CProject

These lemmas allow building CProject proofs by cases on the global type. -/

/-- CProject for end-end. -/
theorem CProject_end (role : String) : CProject .end role .end := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject .end role .end := by simp only [CProjectF]
  exact Eq.mp (congrFun (congrFun (congrFun hfix .end) role) .end) hf

/-- CProject for var-var. -/
theorem CProject_var (t : String) (role : String) : CProject (.var t) role (.var t) := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject (.var t) role (.var t) := by simp only [CProjectF]
  exact Eq.mp (congrFun (congrFun (congrFun hfix (.var t)) role) (.var t)) hf

/-- CProject for mu-mu. -/
theorem CProject_mu (t : String) (body : GlobalType) (candBody : LocalTypeR) (role : String)
    (hcontr : lcontractive body) (hbody : CProject body role candBody) :
    CProject (.mu t body) role (.mu t candBody) := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject (.mu t body) role (.mu t candBody) := by
    dsimp only [CProjectF]
    exact ⟨rfl, hcontr, hbody⟩
  exact Eq.mp (congrFun (congrFun (congrFun hfix (.mu t body)) role) (.mu t candBody)) hf

/-- CProject for comm-send (role is sender). -/
theorem CProject_comm_send (sender receiver : String)
    (gbs : List (Label × GlobalType)) (lbs : List (Label × LocalTypeR))
    (hbranches : BranchesProjRel CProject gbs sender lbs) :
    CProject (.comm sender receiver gbs) sender (.send receiver lbs) := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject (.comm sender receiver gbs) sender (.send receiver lbs) := by
    dsimp only [CProjectF]
    split_ifs with h h'
    · exact ⟨rfl, hbranches⟩           -- sender = sender, take first branch
    · exact absurd rfl h                -- ¬sender = sender ∧ sender = receiver, contradiction
    · exact absurd rfl h                -- ¬sender = sender ∧ ¬sender = receiver, contradiction
  exact Eq.mp (congrFun (congrFun (congrFun hfix (.comm sender receiver gbs)) sender)
    (.send receiver lbs)) hf

/-- CProject for comm-recv (role is receiver). -/
theorem CProject_comm_recv (sender receiver : String)
    (gbs : List (Label × GlobalType)) (lbs : List (Label × LocalTypeR))
    (hns : sender ≠ receiver)
    (hbranches : BranchesProjRel CProject gbs receiver lbs) :
    CProject (.comm sender receiver gbs) receiver (.recv sender lbs) := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject (.comm sender receiver gbs) receiver (.recv sender lbs) := by
    dsimp only [CProjectF]
    -- The if structure is: if receiver = sender then ... else if receiver = receiver then ... else ...
    split_ifs with h1 h2
    · -- h1 : receiver = sender - contradiction since sender ≠ receiver
      exact absurd h1.symm hns
    · -- ¬h1 ∧ h2 : receiver ≠ sender ∧ receiver = receiver - this is the case we want
      exact ⟨rfl, hbranches⟩
    · -- ¬h1 ∧ ¬h2 : receiver ≠ sender ∧ receiver ≠ receiver - contradiction
      exact absurd rfl h2
  exact Eq.mp (congrFun (congrFun (congrFun hfix (.comm sender receiver gbs)) receiver)
    (.recv sender lbs)) hf

/-- CProject for comm-other (role is non-participant). -/
theorem CProject_comm_other (sender receiver role : String)
    (gbs : List (Label × GlobalType)) (cand : LocalTypeR)
    (hns : role ≠ sender) (hnr : role ≠ receiver)
    (hall : AllBranchesProj CProject gbs role cand) :
    CProject (.comm sender receiver gbs) role cand := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject (.comm sender receiver gbs) role cand := by
    unfold CProjectF
    simp only [hns, hnr, ite_false]
    exact hall
  exact Eq.mp (congrFun (congrFun (congrFun hfix (.comm sender receiver gbs)) role) cand) hf

/-! ## Reflection Lemmas

These lemmas characterize the behavior of `projectb` for each constructor case.
We use `sorry` placeholders for now - these will be filled in Phase A when
we establish the CProject coinductive relation. The important part is that
the types are correct. -/

/-- Reflection: projectb for end with end candidate. -/
theorem projectb_end_end (role : String) :
    projectb .end role .end = true := by
  unfold projectb; rfl

/-- Reflection: projectb for end with non-end candidate returns false. -/
theorem projectb_end_var (role t : String) :
    projectb .end role (.var t) = false := by
  unfold projectb; rfl

theorem projectb_end_send (role partner : String) (bs : List (Label × LocalTypeR)) :
    projectb .end role (.send partner bs) = false := by
  unfold projectb; rfl

theorem projectb_end_recv (role partner : String) (bs : List (Label × LocalTypeR)) :
    projectb .end role (.recv partner bs) = false := by
  unfold projectb; rfl

theorem projectb_end_mu (role t : String) (body : LocalTypeR) :
    projectb .end role (.mu t body) = false := by
  unfold projectb; rfl

/-- Reflection: projectb for var-var case. -/
theorem projectb_var_var (t t' : String) (role : String) :
    projectb (.var t) role (.var t') = (t == t') := by
  unfold projectb; rfl

/-- Reflection: projectb for mu-mu case. -/
theorem projectb_mu_mu (t t' : String) (body : GlobalType) (candBody : LocalTypeR) (role : String) :
    projectb (.mu t body) role (.mu t' candBody) =
      (if t == t' then
        if lcontractive body then projectb body role candBody
        else false
      else false) := by
  simp only [projectb]

/-- Reflection: projectb for comm with non-participant. -/
theorem projectb_comm_other
    (sender receiver role : String) (branches : List (Label × GlobalType)) (cand : LocalTypeR)
    (hs : role ≠ sender) (hr : role ≠ receiver) :
    projectb (.comm sender receiver branches) role cand =
      projectbAllBranches branches role cand := by
  have hsender : (role == sender) = false := beq_eq_false_iff_ne.mpr hs
  have hreceiver : (role == receiver) = false := beq_eq_false_iff_ne.mpr hr
  cases branches with
  | nil => unfold projectb projectbAllBranches; simp [hsender, hreceiver]
  | cons head tail =>
      cases head with
      | mk label cont => unfold projectb projectbAllBranches; simp [hsender, hreceiver]

end RumpsteakV2.Protocol.Projection.Projectb
