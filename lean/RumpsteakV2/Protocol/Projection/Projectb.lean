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

private theorem sizeOf_elem_snd_lt_list {α β : Type _} [SizeOf α] [SizeOf β]
    (xs : List (α × β)) (x : α × β) (h : x ∈ xs) :
    sizeOf x.2 < sizeOf xs := by
  induction xs with
  | nil => simp at h
  | cons hd tl ih =>
      cases h with
      | head => simp only [sizeOf, List._sizeOf_1, Prod._sizeOf_1]; omega
      | tail _ hmem => have := ih hmem; simp only [sizeOf, List._sizeOf_1] at *; omega

private theorem sizeOf_elem_snd_lt_comm (sender receiver : String)
    (gbs : List (Label × GlobalType)) (gb : Label × GlobalType) (h : gb ∈ gbs) :
    sizeOf gb.2 < sizeOf (GlobalType.comm sender receiver gbs) := by
  have h1 := sizeOf_elem_snd_lt_list gbs gb h
  have h2 := sizeOf_bs_lt_comm sender receiver gbs
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
    | (_, cont) :: rest, role, cand =>
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

/-- Unfolding-insensitive generator for CProject.
    This mirrors Coq's `UnfProj` wrapper: we project on fully-unfolded
    global and local types. -/
def CProjectF_unfold (R : ProjRel) : ProjRel := fun g role cand =>
  CProjectF R (GlobalType.fullUnfold g) role (LocalTypeR.fullUnfold cand)

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

private theorem CProjectF_unfold_mono : Monotone CProjectF_unfold := by
  intro R S h g role cand hrel
  exact CProjectF_mono h _ _ _ hrel

/-- CProject as the greatest fixed point of CProjectF.
    Uses the pointwise complete lattice structure on ProjRel. -/
def CProject : ProjRel :=
  OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩

/-- Unfolding-insensitive projection (Coq-style).
    This is the gfp of CProjectF_unfold and is the target for the
    Project_EQ2 refactor. -/
def CProjectU : ProjRel :=
  OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩

private theorem CProject_fixed : CProjectF CProject = CProject := by
  simpa [CProject] using (OrderHom.isFixedPt_gfp ⟨CProjectF, CProjectF_mono⟩)

private theorem CProjectU_fixed : CProjectF_unfold CProjectU = CProjectU := by
  simpa [CProjectU] using (OrderHom.isFixedPt_gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩)

/-- Coinduction principle for CProject: if R ⊆ CProjectF R, then R ⊆ CProject. -/
theorem CProject_coind {R : ProjRel} (h : ∀ g role cand, R g role cand → CProjectF R g role cand) :
    ∀ g role cand, R g role cand → CProject g role cand := by
  intro g role cand hr
  have hle : R ≤ CProjectF R := fun x y z hxyz => h x y z hxyz
  have hgfp : R ≤ CProject := OrderHom.le_gfp ⟨CProjectF, CProjectF_mono⟩ hle
  exact hgfp g role cand hr

theorem CProjectU_coind {R : ProjRel}
    (h : ∀ g role cand, R g role cand → CProjectF_unfold R g role cand) :
    ∀ g role cand, R g role cand → CProjectU g role cand := by
  intro g role cand hr
  have hle : R ≤ CProjectF_unfold R := fun x y z hxyz => h x y z hxyz
  have hgfp : R ≤ CProjectU := OrderHom.le_gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩ hle
  exact hgfp g role cand hr

/-- Destruct CProject: if CProject holds, then CProjectF CProject holds. -/
theorem CProject_destruct {g : GlobalType} {role : String} {cand : LocalTypeR}
    (h : CProject g role cand) : CProjectF CProject g role cand := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  exact Eq.mp (congrFun (congrFun (congrFun hfix.symm g) role) cand) h

theorem CProjectU_destruct {g : GlobalType} {role : String} {cand : LocalTypeR}
    (h : CProjectU g role cand) : CProjectF_unfold CProjectU g role cand := by
  have hfix : CProjectF_unfold CProjectU = CProjectU := CProjectU_fixed
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
They provide the computational behavior that the soundness and completeness
proofs rely on. -/

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

/-! ## Soundness and Completeness

These theorems establish the correspondence between the boolean checker `projectb`
and the coinductive relation `CProject`. -/

/-- Helper: convert BEq equality to Prop equality for String. -/
private theorem string_beq_eq_true_to_eq {a b : String} (h : (a == b) = true) : a = b := by
  exact eq_of_beq h

/-- Helper: PayloadSort BEq true implies equality.
    Proven by induction since PayloadSort has recursive prod constructor. -/
private theorem payloadSort_beq_eq_true_to_eq {a b : PayloadSort} (h : (a == b) = true) : a = b := by
  induction a generalizing b with
  | unit => cases b <;> simp_all [reduceBEq]
  | nat => cases b <;> simp_all [reduceBEq]
  | bool => cases b <;> simp_all [reduceBEq]
  | string => cases b <;> simp_all [reduceBEq]
  | prod s1 s2 ih1 ih2 =>
      cases b with
      | prod t1 t2 =>
          simp only [reduceBEq, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          simp only [ih1 h1, ih2 h2]
      | _ => simp_all [reduceBEq]

/-- Helper: convert BEq equality to Prop equality for Label.
    Uses reduceBEq simproc to unfold derived BEq to component-wise form. -/
private theorem label_beq_eq_true_to_eq {a b : Label} (h : (a == b) = true) : a = b := by
  -- Destruct Label to access components
  cases a with | mk n1 s1 =>
  cases b with | mk n2 s2 =>
  -- Use reduceBEq to unfold the derived BEq to (n1 == n2) && (s1 == s2)
  simp only [reduceBEq, Bool.and_eq_true] at h
  obtain ⟨hn, hs⟩ := h
  -- String has LawfulBEq, so eq_of_beq works
  have heq_n : n1 = n2 := eq_of_beq hn
  -- PayloadSort: use our helper
  have heq_s : s1 = s2 := payloadSort_beq_eq_true_to_eq hs
  simp only [heq_n, heq_s]

/-- Helper: PayloadSort beq is reflexive. -/
private theorem payloadSort_beq_refl (s : PayloadSort) : (s == s) = true := by
  induction s with
  | unit => rfl
  | nat => rfl
  | bool => rfl
  | string => rfl
  | prod s1 s2 ih1 ih2 =>
      simp only [reduceBEq, Bool.and_eq_true]
      exact ⟨ih1, ih2⟩

/-- Helper: convert Prop equality to BEq equality for Label. -/
private theorem eq_to_label_beq_eq_true {a b : Label} (h : a = b) : (a == b) = true := by
  subst h
  cases a with | mk n s =>
  simp only [reduceBEq, beq_self_eq_true, Bool.true_and, payloadSort_beq_refl]

/-- Relation for coinduction in projectb_sound: pairs where projectb returns true. -/
private def SoundRel : ProjRel := fun g role cand => projectb g role cand = true

/-- Helper: split Bool.and = true into two parts. -/
private theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- Helper: projectbBranches true implies BranchesProjRel SoundRel. -/
private theorem projectbBranches_to_SoundRel
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List (Label × LocalTypeR))
    (h : projectbBranches gbs role lbs = true) :
    BranchesProjRel SoundRel gbs role lbs := by
  induction gbs generalizing lbs with
  | nil =>
      cases lbs with
      | nil => exact List.Forall₂.nil
      | cons _ _ =>
          unfold projectbBranches at h
          exact False.elim (Bool.false_ne_true h)
  | cons ghd gtl ih =>
      cases lbs with
      | nil =>
          unfold projectbBranches at h
          exact False.elim (Bool.false_ne_true h)
      | cons lhd ltl =>
          unfold projectbBranches at h
          split_ifs at h with hlabel
          -- Only one goal: hlabel = true (the false branch is eliminated since false = true is absurd)
          have ⟨hproj, hrest⟩ := bool_and_true h
          have hlabel' : ghd.1 = lhd.1 := label_beq_eq_true_to_eq hlabel
          exact List.Forall₂.cons ⟨hlabel', hproj⟩ (ih ltl hrest)

/-- Helper: projectbAllBranches true implies AllBranchesProj SoundRel. -/
private theorem projectbAllBranches_to_SoundRel
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (h : projectbAllBranches gbs role cand = true) :
    AllBranchesProj SoundRel gbs role cand := by
  induction gbs with
  | nil =>
      intro gb hgb
      cases hgb
  | cons ghd gtl ih =>
      intro gb hgb
      unfold projectbAllBranches at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hhead, hrest⟩ := h
      cases hgb with
      | head _ => exact hhead
      | tail _ hmem => exact ih hrest gb hmem

/-- SoundRel is a post-fixpoint of CProjectF. -/
private theorem SoundRel_postfix : ∀ g role cand, SoundRel g role cand → CProjectF SoundRel g role cand := by
  intro g role cand h
  unfold SoundRel at h
  cases g with
  | «end» =>
      cases cand with
      | «end» => simp only [CProjectF]
      | var _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | send _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | recv _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | mu _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
  | var t =>
      cases cand with
      | «end» => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | var t' =>
          simp only [CProjectF]
          simp only [projectb] at h
          exact string_beq_eq_true_to_eq h
      | send _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | recv _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | mu _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
  | mu t body =>
      cases cand with
      | «end» => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | var _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | send _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | recv _ _ => simp only [projectb] at h; exact False.elim (Bool.false_ne_true h)
      | mu t' candBody =>
          simp only [projectb] at h
          split_ifs at h with ht hcontr
          -- Only one goal remains: ht = true ∧ hcontr = true (other branches give false = true)
          simp only [CProjectF]
          refine ⟨string_beq_eq_true_to_eq ht, hcontr, h⟩
  | comm sender receiver gbs =>
      unfold projectb at h
      split_ifs at h with hs hr
      · -- sender case: role == sender
        cases cand with
        | «end» => exact False.elim (Bool.false_ne_true h)
        | var _ => exact False.elim (Bool.false_ne_true h)
        | send partner lbs =>
            dsimp only at h
            split_ifs at h with hpartner
            -- Only true case remains (false = true is absurd)
            dsimp only [CProjectF]
            split_ifs with hs' hr'
            · -- hs' : role = sender - this is the correct case
              exact ⟨string_beq_eq_true_to_eq hpartner, projectbBranches_to_SoundRel gbs role lbs h⟩
            · -- hs' : ¬role = sender - contradicts hs
              exact absurd (string_beq_eq_true_to_eq hs) hs'
            · -- hs' : ¬role = sender AND hr' : ¬role = receiver - contradicts hs
              exact absurd (string_beq_eq_true_to_eq hs) hs'
        | recv _ _ => exact False.elim (Bool.false_ne_true h)
        | mu _ _ => exact False.elim (Bool.false_ne_true h)
      · -- receiver case: role == receiver
        cases cand with
        | «end» => exact False.elim (Bool.false_ne_true h)
        | var _ => exact False.elim (Bool.false_ne_true h)
        | send _ _ => exact False.elim (Bool.false_ne_true h)
        | recv partner lbs =>
            dsimp only at h
            split_ifs at h with hpartner
            -- Only true case remains
            dsimp only [CProjectF]
            split_ifs with hs' hr'
            · -- hs' : role = sender - contradiction since role ≠ sender
              have hne : role ≠ sender := fun heq => by
                subst heq
                simp only [beq_self_eq_true] at hs
                exact absurd trivial hs
              exact absurd hs' hne
            · exact ⟨string_beq_eq_true_to_eq hpartner, projectbBranches_to_SoundRel gbs role lbs h⟩
            · exact absurd (string_beq_eq_true_to_eq hr) hr'
        | mu _ _ => exact False.elim (Bool.false_ne_true h)
      · -- non-participant case
        dsimp only [CProjectF]
        split_ifs with hs' hr'
        · -- hs' : role = sender contradicts hs (role ≠ sender as Bool)
          subst hs'
          simp only [beq_self_eq_true] at hs
          exact absurd trivial hs
        · -- hr' : role = receiver contradicts hr (role ≠ receiver as Bool)
          subst hr'
          simp only [beq_self_eq_true] at hr
          exact absurd trivial hr
        · exact projectbAllBranches_to_SoundRel gbs role cand h

/-- Soundness: if projectb returns true, then CProject holds. -/
theorem projectb_sound (g : GlobalType) (role : String) (cand : LocalTypeR)
    (h : projectb g role cand = true) : CProject g role cand := by
  have hinR : SoundRel g role cand := h
  exact CProject_coind SoundRel_postfix g role cand hinR

/-- Helper: BranchesProjRel CProject implies projectbBranches.
    The ih provides recursive evidence that for each branch global type,
    if CProject holds then projectb returns true. -/
private theorem BranchesProjRel_to_projectbBranches
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List (Label × LocalTypeR))
    (hrel : BranchesProjRel CProject gbs role lbs)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectbBranches gbs role lbs = true := by
  induction hrel with
  | nil => simp only [projectbBranches]
  | @cons ghd lhd gtl ltl hpair hrest ihrest =>
      obtain ⟨hlabel, hproj⟩ := hpair
      unfold projectbBranches
      -- hlabel : ghd.1 = lhd.1, so we need (ghd.1 == lhd.1) = true
      have hbeq : (ghd.1 == lhd.1) = true := eq_to_label_beq_eq_true hlabel
      simp only [hbeq, ↓reduceIte, Bool.and_eq_true]
      constructor
      · exact ih ghd (List.Mem.head gtl) lhd.2 hproj
      · exact ihrest (fun gb hmem lb hcp => ih gb (List.Mem.tail ghd hmem) lb hcp)

/-- Helper: AllBranchesProj CProject implies projectbAllBranches.
    The ih provides recursive evidence that for each branch global type,
    if CProject holds then projectb returns true. -/
private theorem AllBranchesProj_to_projectbAllBranches
    (gbs : List (Label × GlobalType)) (role : String) (cand : LocalTypeR)
    (hall : AllBranchesProj CProject gbs role cand)
    (ih : ∀ gb ∈ gbs, CProject gb.2 role cand → projectb gb.2 role cand = true) :
    projectbAllBranches gbs role cand = true := by
  induction gbs with
  | nil => simp only [projectbAllBranches]
  | cons ghd gtl ihtl =>
      unfold projectbAllBranches
      simp only [Bool.and_eq_true]
      constructor
      · exact ih ghd (List.Mem.head gtl) (hall ghd (List.Mem.head gtl))
      · exact ihtl (fun gb hgb => hall gb (List.Mem.tail ghd hgb))
            (fun gb hmem hcp => ih gb (List.Mem.tail ghd hmem) hcp)

/-- Completeness: if CProject holds, then projectb returns true.
    Proven by well-founded recursion on g. -/
theorem projectb_complete (g : GlobalType) (role : String) (cand : LocalTypeR)
    (h : CProject g role cand) : projectb g role cand = true := by
  -- Use CProject_destruct to access the CProjectF structure
  have hF := CProject_destruct h
  -- Case split on g and cand using CProjectF structure
  cases hg : g with
  | «end» =>
      subst hg  -- Substitute g = GlobalType.end first
      dsimp only [CProjectF] at hF
      cases cand with
      | «end» => simp only [projectb]
      | _ => exact False.elim (by simp_all)
  | var t =>
      subst hg  -- Substitute g = GlobalType.var t first
      dsimp only [CProjectF] at hF
      cases cand with
      | var t' =>
          simp only [projectb]
          subst hF  -- Now hF : t = t'
          simp only [beq_self_eq_true]
      | _ => exact False.elim (by simp_all)
  | mu t body =>
      simp only [hg, CProjectF] at hF
      cases cand with
      | mu t' candBody =>
          obtain ⟨heq, hcontr, hbody⟩ := hF
          subst heq
          simp only [projectb, beq_self_eq_true, hcontr, ↓reduceIte]
          exact projectb_complete body role candBody hbody
      | «end» => exact hF.elim
      | var _ => exact hF.elim
      | send _ _ => exact hF.elim
      | recv _ _ => exact hF.elim
  | comm sender receiver gbs =>
      simp only [hg, CProjectF] at hF
      split_ifs at hF with hs hr
      · -- hs : role = sender
        cases cand with
        | send partner lbs =>
            obtain ⟨hpartner, hbranches⟩ := hF
            simp only [projectb]
            subst hs hpartner
            simp only [beq_self_eq_true, ↓reduceIte]
            exact BranchesProjRel_to_projectbBranches gbs role lbs hbranches
              (fun gb hmem lb hcp => projectb_complete gb.2 role lb hcp)
        | «end» => exact False.elim hF
        | var _ => exact False.elim hF
        | recv _ _ => exact False.elim hF
        | mu _ _ => exact False.elim hF
      · -- hr : role = receiver, hs : ¬(role = sender)
        cases cand with
        | recv partner lbs =>
            obtain ⟨hpartner, hbranches⟩ := hF
            simp only [projectb]
            have hne : (role == sender) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; exact hs
            simp only [hne]
            subst hr hpartner
            simp only [beq_self_eq_true, ↓reduceIte]
            exact BranchesProjRel_to_projectbBranches gbs role lbs hbranches
              (fun gb hmem lb hcp => projectb_complete gb.2 role lb hcp)
        | «end» => exact False.elim hF
        | var _ => exact False.elim hF
        | send _ _ => exact False.elim hF
        | mu _ _ => exact False.elim hF
      · -- non-participant: hs : ¬(role = sender), hr : ¬(role = receiver)
        subst hg
        unfold projectb
        have hne_s : (role == sender) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact hs
        have hne_r : (role == receiver) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact hr
        simp only [hne_s, hne_r]
        exact AllBranchesProj_to_projectbAllBranches gbs role cand hF
          (fun gb hmem hcp => projectb_complete gb.2 role cand hcp)
termination_by g
decreasing_by
  all_goals
    -- Now we have context like: hg : g = GlobalType... and hmem : gb ∈ gbs
    -- Use cases to match which termination goal we're in
    first
    -- mu case: sizeOf body < sizeOf g where g = GlobalType.mu t body
    | (subst_vars; exact sizeOf_body_lt_mu _ _)
    -- comm case: sizeOf gb.2 < sizeOf g where g = GlobalType.comm s r gbs and gb ∈ gbs
    | (subst_vars; apply sizeOf_elem_snd_lt_comm; assumption)

/-- projectb = true iff CProject holds. -/
theorem projectb_iff_CProject (g : GlobalType) (role : String) (cand : LocalTypeR) :
    projectb g role cand = true ↔ CProject g role cand :=
  ⟨projectb_sound g role cand, projectb_complete g role cand⟩

end RumpsteakV2.Protocol.Projection.Projectb
