import Choreography.Projection.Projectb.Part1

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

/-! # Projectb Part 2

Coinductive CProject relation, constructor lemmas, and reflection lemmas connecting
`projectb` to `CProject`.
-/

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
  | .mu t body, cand =>
      -- Preserve mu when the projected body is guarded; otherwise collapse to .end.
      ∃ candBody, R body role candBody ∧
        ((candBody.isGuarded t = true ∧ cand = .mu t candBody) ∨
         (candBody.isGuarded t = false ∧ cand = .end))
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

/-- One-step generator for CProjectU (fully-unfolded).
    This mirrors Coq's `project_gen`: add a non-participant end case and
    require uniform participation (`part_of_all2`) for non-participant comms. -/
def CProjectF_unfold_core (R : ProjRel) : ProjRel := fun g role cand =>
  (¬ part_of2 role g ∧ cand = .end) ∨
    match g, cand with
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
          (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj R gbs role cand
    | _, _ => CProjectF R g role cand

/-- Unfolding-insensitive generator for CProject.
    This mirrors Coq's `UnfProj` wrapper: we project on fully-unfolded
    global and local types. -/
def CProjectF_unfold (R : ProjRel) : ProjRel := fun g role cand =>
  g.wellFormed = true ∧ LocalTypeR.WellFormed cand ∧
    CProjectF_unfold_core R (GlobalType.fullUnfoldIter g) role (LocalTypeR.fullUnfold cand)

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
       exact ⟨h1, h _ _ _ h2, h3⟩)
    | (-- comm cases with if-then-else structure
       split_ifs at hrel ⊢
       all_goals
         first
         | exact hrel
         | (obtain ⟨h1, h2⟩ := hrel; exact ⟨h1, BranchesProjRel_mono h h2⟩)
         | exact AllBranchesProj_mono h hrel)

/-- Helper: monotonicity for the non-participant comm branch. -/
private theorem CProjectF_unfold_core_mono_comm_other
    {R S : ProjRel} (h : ∀ g r c, R g r c → S g r c)
    {gbs : List (Label × GlobalType)} {role : String} {cand : LocalTypeR}
    (hcore :
      (∀ (a : Label) (b : GlobalType), (a, b) ∈ gbs → part_of_all2 role b) ∧
        AllBranchesProj R gbs role cand) :
    (∀ (a : Label) (b : GlobalType), (a, b) ∈ gbs → part_of_all2 role b) ∧
      AllBranchesProj S gbs role cand := by
  -- Preserve the participation side-condition and lift the branch relation.
  exact ⟨hcore.1, AllBranchesProj_mono h hcore.2⟩

private theorem CProjectF_unfold_core_mono_comm_send
    {R S : ProjRel} (h : ∀ g r c, R g r c → S g r c)
    {sender receiver role : String} {gbs : List (Label × GlobalType)}
    {partner : String} {lbs : List (Label × LocalTypeR)}
    (hcore :
      (if role = sender then partner = receiver ∧ BranchesProjRel R gbs role lbs
       else if role = receiver then False
       else (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj R gbs role (.send partner lbs))) :
    (if role = sender then partner = receiver ∧ BranchesProjRel S gbs role lbs
     else if role = receiver then False
     else (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj S gbs role (.send partner lbs)) := by
  -- Sender case lifts BranchesProjRel; non-participant case lifts AllBranchesProj.
  by_cases hrs : role = sender
  · simp [hrs] at hcore ⊢
    obtain ⟨h1, h2⟩ := hcore
    exact ⟨h1, BranchesProjRel_mono h h2⟩
  · by_cases hrr : role = receiver
    · have hne : receiver ≠ sender := by
        intro h
        exact hrs (hrr.trans h)
      simp [hrr, hne] at hcore ⊢
    · simp [hrs, hrr] at hcore ⊢
      exact CProjectF_unfold_core_mono_comm_other h hcore

private theorem CProjectF_unfold_core_mono_comm_recv
    {R S : ProjRel} (h : ∀ g r c, R g r c → S g r c)
    {sender receiver role : String} {gbs : List (Label × GlobalType)}
    {partner : String} {lbs : List (Label × LocalTypeR)}
    (hcore :
      (if role = sender then False
       else if role = receiver then partner = sender ∧ BranchesProjRel R gbs role lbs
       else (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj R gbs role (.recv partner lbs))) :
    (if role = sender then False
     else if role = receiver then partner = sender ∧ BranchesProjRel S gbs role lbs
     else (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj S gbs role (.recv partner lbs)) := by
  -- Receiver case lifts BranchesProjRel; non-participant case lifts AllBranchesProj.
  by_cases hrs : role = sender
  · simp [hrs] at hcore ⊢
  · by_cases hrr : role = receiver
    · have hcore' :
          receiver ≠ sender ∧ partner = sender ∧ BranchesProjRel R gbs receiver lbs := by
        simpa [hrs, hrr] using hcore
      rcases hcore' with ⟨hns, hpartner, hbranches⟩
      have hgoal :
          receiver ≠ sender ∧ partner = sender ∧ BranchesProjRel S gbs receiver lbs :=
        ⟨hns, hpartner, BranchesProjRel_mono h hbranches⟩
      simpa [hrs, hrr] using hgoal
    · simp [hrs, hrr] at hcore ⊢
      exact CProjectF_unfold_core_mono_comm_other h hcore

private theorem CProjectF_unfold_core_mono_comm_other_cand
    {R S : ProjRel} (h : ∀ g r c, R g r c → S g r c)
    {sender receiver role : String} {gbs : List (Label × GlobalType)} {cand : LocalTypeR}
    (hcore :
      (if role = sender then False
       else if role = receiver then False
       else (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj R gbs role cand)) :
    (if role = sender then False
     else if role = receiver then False
     else (∀ pair, pair ∈ gbs → part_of_all2 role pair.2) ∧ AllBranchesProj S gbs role cand) := by
  -- Only the non-participant branch is possible for other candidates.
  by_cases hrs : role = sender
  · simp [hrs] at hcore ⊢
  · by_cases hrr : role = receiver
    · simp [hrr] at hcore ⊢
    · simp [hrs, hrr] at hcore ⊢
      exact CProjectF_unfold_core_mono_comm_other h hcore

/-! ### Monotonicity for CProjectF_unfold_core -/

private theorem CProjectF_unfold_core_mono : Monotone CProjectF_unfold_core := by
  intro R S h g role cand hrel
  rcases hrel with hnonpart | hcore
  · exact Or.inl hnonpart
  · refine Or.inr ?_
    cases g with
    | «end» =>
        -- Non-comm cases reduce to CProjectF monotonicity.
        have : CProjectF S .end role cand := CProjectF_mono h _ _ _ hcore
        simpa [CProjectF_unfold_core, CProjectF] using this
    | var _ =>
        have : CProjectF S (.var _) role cand := CProjectF_mono h _ _ _ hcore
        simpa [CProjectF_unfold_core, CProjectF] using this
    | mu _ _ =>
        have : CProjectF S (.mu _ _) role cand := CProjectF_mono h _ _ _ hcore
        simpa [CProjectF_unfold_core, CProjectF] using this
    | comm sender receiver gbs =>
        cases cand with
        | send partner lbs =>
            exact CProjectF_unfold_core_mono_comm_send h hcore
        | recv partner lbs =>
            exact CProjectF_unfold_core_mono_comm_recv h hcore
        | «end» =>
            exact CProjectF_unfold_core_mono_comm_other_cand h hcore
        | var _ =>
            exact CProjectF_unfold_core_mono_comm_other_cand h hcore
        | mu _ _ =>
            exact CProjectF_unfold_core_mono_comm_other_cand h hcore

private theorem CProjectF_unfold_mono : Monotone CProjectF_unfold := by
  intro R S h g role cand hrel
  rcases hrel with ⟨hwf, hWFcand, hproj⟩
  exact ⟨hwf, hWFcand, CProjectF_unfold_core_mono h _ _ _ hproj⟩
instance : CoinductiveRel ProjRel CProjectF := ⟨CProjectF_mono⟩

instance : CoinductiveRel ProjRel CProjectF_unfold := ⟨CProjectF_unfold_mono⟩


/-- CProject as the greatest fixed point of CProjectF.
    Uses the pointwise complete lattice structure on ProjRel. -/
def CProject : ProjRel :=
  OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩

/-- Unfolding-insensitive projection (Coq-style).
    This is the gfp of CProjectF_unfold and is the target for the
    Project_EQ2 refactor. -/
def CProjectU : ProjRel :=
  OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩

/-! Shared coinduction aliases (see `CoinductiveRel`). -/
/-- Alias: CProject as gfp via CoinductiveRel. -/
theorem CProject_gfp : CProject = SessionCoTypes.CoinductiveRel.gfp (F := CProjectF) := rfl

/-- Alias: CProjectU as gfp via CoinductiveRel. -/
theorem CProjectU_gfp : CProjectU = SessionCoTypes.CoinductiveRel.gfp (F := CProjectF_unfold) := rfl

/-- Alias: coinduction via CoinductiveRel for CProject. -/
theorem CProject_coind' {R : ProjRel} (h : R ≤ CProjectF R) : R ≤ CProject := by
  simpa [CProject] using (SessionCoTypes.CoinductiveRel.coind (F := CProjectF) h)

/-- Alias: coinduction via CoinductiveRel for CProjectU. -/
theorem CProjectU_coind' {R : ProjRel} (h : R ≤ CProjectF_unfold R) : R ≤ CProjectU := by
  simpa [CProjectU] using (SessionCoTypes.CoinductiveRel.coind (F := CProjectF_unfold) h)

/-- Alias: unfold via CoinductiveRel for CProject. -/
theorem CProject_unfold' : CProject ≤ CProjectF CProject := by
  change (OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩) ≤
    CProjectF (OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩)
  exact SessionCoTypes.CoinductiveRel.unfold (F := CProjectF)

/-- Alias: fold via CoinductiveRel for CProject. -/
theorem CProject_fold' : CProjectF CProject ≤ CProject := by
  change CProjectF (OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩) ≤
    OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩
  exact SessionCoTypes.CoinductiveRel.fold (F := CProjectF)

/-- Alias: unfold via CoinductiveRel for CProjectU. -/
theorem CProjectU_unfold' : CProjectU ≤ CProjectF_unfold CProjectU := by
  change (OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩) ≤
    CProjectF_unfold (OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩)
  exact SessionCoTypes.CoinductiveRel.unfold (F := CProjectF_unfold)

/-- Alias: fold via CoinductiveRel for CProjectU. -/
theorem CProjectU_fold' : CProjectF_unfold CProjectU ≤ CProjectU := by
  change CProjectF_unfold (OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩) ≤
    OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩
  exact SessionCoTypes.CoinductiveRel.fold (F := CProjectF_unfold)

private theorem CProject_fixed : CProjectF CProject = CProject := by
  change CProjectF (OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩) =
    OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩
  exact SessionCoTypes.CoinductiveRel.gfp_fixed (F := CProjectF)

private theorem CProjectU_fixed : CProjectF_unfold CProjectU = CProjectU := by
  change CProjectF_unfold (OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩) =
    OrderHom.gfp ⟨CProjectF_unfold, CProjectF_unfold_mono⟩
  exact SessionCoTypes.CoinductiveRel.gfp_fixed (F := CProjectF_unfold)

/-- Coinduction principle for CProject: if R ⊆ CProjectF R, then R ⊆ CProject. -/
theorem CProject_coind {R : ProjRel} (h : ∀ g role cand, R g role cand → CProjectF R g role cand) :
    ∀ g role cand, R g role cand → CProject g role cand := by
  intro g role cand hr
  have hle : R ≤ CProjectF R := fun x y z hxyz => h x y z hxyz
  exact (CProject_coind' hle) g role cand hr

/-- Coinduction principle for CProjectU: if R ⊆ CProjectF_unfold R, then R ⊆ CProjectU. -/
theorem CProjectU_coind {R : ProjRel}
    (h : ∀ g role cand, R g role cand → CProjectF_unfold R g role cand) :
    ∀ g role cand, R g role cand → CProjectU g role cand := by
  intro g role cand hr
  have hle : R ≤ CProjectF_unfold R := fun x y z hxyz => h x y z hxyz
  exact (CProjectU_coind' hle) g role cand hr

/-- Destruct CProject: if CProject holds, then CProjectF CProject holds. -/
theorem CProject_destruct {g : GlobalType} {role : String} {cand : LocalTypeR}
    (h : CProject g role cand) : CProjectF CProject g role cand := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  exact Eq.mp (congrFun (congrFun (congrFun hfix.symm g) role) cand) h

/-- Destruct CProjectU: if CProjectU holds, then CProjectF_unfold CProjectU holds. -/
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

/-- CProject for mu-mu.
    Now requires candBody.isGuarded t to match new trans semantics. -/
theorem CProject_mu (t : String) (body : GlobalType) (candBody : LocalTypeR) (role : String)
    (hguard : candBody.isGuarded t = true) (hbody : CProject body role candBody) :
    CProject (.mu t body) role (.mu t candBody) := by
  have hfix : CProjectF CProject = CProject := CProject_fixed
  have hf : CProjectF CProject (.mu t body) role (.mu t candBody) := by
    dsimp only [CProjectF]
    refine ⟨candBody, hbody, Or.inl ?_⟩
    exact ⟨hguard, rfl⟩
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

/-- Reflection: projectb for end with send candidate returns false. -/
theorem projectb_end_send (role partner : String) (bs : List (Label × LocalTypeR)) :
    projectb .end role (.send partner bs) = false := by
  unfold projectb; rfl

/-- Reflection: projectb for end with recv candidate returns false. -/
theorem projectb_end_recv (role partner : String) (bs : List (Label × LocalTypeR)) :
    projectb .end role (.recv partner bs) = false := by
  unfold projectb; rfl

/-- Reflection: projectb for end with mu candidate returns false. -/
theorem projectb_end_mu (role t : String) (body : LocalTypeR) :
    projectb .end role (.mu t body) = false := by
  unfold projectb; rfl

/-- Reflection: projectb for var-var case. -/
theorem projectb_var_var (t t' : String) (role : String) :
    projectb (.var t) role (.var t') = (t == t') := by
  unfold projectb; rfl

/-- Reflection: projectb for mu-mu case.
    Note: We check `candBody.isGuarded t'` (Coq-style) instead of `lcontractive body`. -/
theorem projectb_mu_mu (t t' : String) (body : GlobalType) (candBody : LocalTypeR) (role : String) :
    projectb (.mu t body) role (.mu t' candBody) =
      (if t == t' then
        if candBody.isGuarded t' then projectb body role candBody
        else false
      else false) := by
  simp only [projectb]

/-- Reflection: projectb for mu-end case. -/
theorem projectb_mu_end (t : String) (body : GlobalType) (role : String) :
    projectb (.mu t body) role .end =
      (let candBody := Trans.trans body role
       if candBody.isGuarded t then false else projectb body role candBody) := by
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

end Choreography.Projection.Projectb
