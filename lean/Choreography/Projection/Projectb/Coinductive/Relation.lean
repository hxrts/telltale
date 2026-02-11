import Choreography.Projection.Projectb.Checker

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-! # Choreography.Projection.Projectb.Coinductive

Coinductive CProject relation, constructor lemmas, and reflection lemmas connecting
`projectb` to `CProject`.
-/

/-
The Problem. Projection must handle recursive global types, which requires a
coinductive definition. The boolean checker `projectb` is executable but we need
a relational specification `CProject` for reasoning about projection properties.

Solution Structure. We define:
1. `CProjectF`: one-step generator for the projection relation
2. `CProject`: greatest fixed point of CProjectF (coinductive relation)
3. Constructor lemmas for building CProject witnesses
4. Reflection lemmas connecting `projectb = true` to `CProject`
-/

/-! ## CProject Coinductive Relation

CProject is defined as the greatest fixed point of CProjectF, which captures
one step of the projection relation. This is analogous to how EQ2 is defined
for local type equality. -/

/-- Ternary relation for projection. -/
abbrev ProjRel := GlobalType → String → LocalTypeR → Prop

/-- Branch-wise projection relation for send/recv. -/
def BranchesProjRel (R : ProjRel)
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR) : Prop :=
  List.Forall₂ (fun gb lb => gb.1 = lb.1 ∧ lb.2.1 = none ∧ R gb.2 role lb.2.2) gbs lbs

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
  | .delegate p q sid r cont, cand =>
      if role = p then
        -- delegator: sends the capability (single branch)
        match cand with
        | .send partner [(lbl, vt, contCand)] =>
            partner = q ∧
              lbl = ⟨"_delegate", .unit⟩ ∧
              vt = some (.chan sid r) ∧
              R cont role contCand
        | _ => False
      else if role = q then
        -- delegatee: receives the capability (single branch)
        match cand with
        | .recv partner [(lbl, vt, contCand)] =>
            partner = p ∧
              lbl = ⟨"_delegate", .unit⟩ ∧
              vt = some (.chan sid r) ∧
              R cont role contCand
        | _ => False
      else
        -- non-participant: follows continuation
        R cont role cand
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
      exact List.Forall₂.cons ⟨hpair.1, hpair.2.1, h _ _ _ hpair.2.2⟩ ih

private theorem AllBranchesProj_mono {R S : ProjRel}
    (h : ∀ g r c, R g r c → S g r c) :
    ∀ {gbs role cand}, AllBranchesProj R gbs role cand → AllBranchesProj S gbs role cand := by
  intro gbs role cand hall gb hgb
  exact h _ _ _ (hall gb hgb)

private theorem CProjectF_mono : Monotone CProjectF := by
  intro R S h g role cand hrel
  cases g with
  | «end» =>
      cases cand <;> simpa [CProjectF] using hrel
  | var t =>
      cases cand <;> simpa [CProjectF] using hrel
  | mu t body =>
      cases cand with
      | mu t' candBody =>
          simp [CProjectF] at hrel ⊢
          rcases hrel with ⟨hbody, hguard, ht⟩
          exact ⟨h _ _ _ hbody, hguard, ht⟩
      | «end» =>
          simp [CProjectF] at hrel ⊢
          rcases hrel with ⟨candBody, hbody, hguard⟩
          exact ⟨candBody, h _ _ _ hbody, hguard⟩
      | var _ =>
          simp [CProjectF] at hrel
      | send _ _ =>
          simp [CProjectF] at hrel
      | recv _ _ =>
          simp [CProjectF] at hrel
  | comm sender receiver gbs =>
      by_cases hs : role = sender
      · cases cand with
        | send partner lbs =>
            simp [CProjectF, hs] at hrel ⊢
            rcases hrel with ⟨h1, h2⟩
            exact ⟨h1, BranchesProjRel_mono h h2⟩
        | _ =>
            simp [CProjectF, hs] at hrel ⊢
      · by_cases hr : role = receiver
        · have hns : receiver ≠ sender := by
            intro h
            exact hs (hr.trans h)
          cases cand with
          | recv partner lbs =>
              simp [CProjectF, hr, hns] at hrel ⊢
              rcases hrel with ⟨h1, h2⟩
              exact ⟨h1, BranchesProjRel_mono h h2⟩
          | _ =>
              simp [CProjectF, hr, hns] at hrel ⊢
        · simp [CProjectF, hs, hr] at hrel ⊢
          exact AllBranchesProj_mono h hrel
  | delegate p q sid r cont =>
      by_cases hp : role = p
      · cases cand with
        | send partner lbs =>
            simp [CProjectF, hp] at hrel ⊢
            cases lbs with
            | nil => simpa using hrel
            | cons b bs =>
                cases bs with
                | nil =>
                    cases b with
                    | mk lbl rest =>
                        cases rest with
                        | mk vt contCand =>
                            have hrel' :
                                partner = q ∧ lbl = ⟨"_delegate", .unit⟩ ∧
                                  vt = some (.chan sid r) ∧ R cont p contCand := by
                              simpa [and_left_comm, and_assoc] using hrel
                            rcases hrel' with ⟨h1, h2, h3, h4⟩
                            exact ⟨h1, h2, h3, h _ _ _ h4⟩
                | cons _ _ =>
                    simpa using hrel
        | _ =>
            simp [CProjectF, hp] at hrel ⊢
      · by_cases hq : role = q
        · have hnp : q ≠ p := by
            intro hqp
            exact hp (hq.trans hqp)
          cases cand with
          | recv partner lbs =>
              simp [CProjectF, hq, hnp] at hrel ⊢
              cases lbs with
              | nil => simpa using hrel
              | cons b bs =>
                  cases bs with
                  | nil =>
                      cases b with
                      | mk lbl rest =>
                          cases rest with
                          | mk vt contCand =>
                              have hrel' :
                                  partner = p ∧ lbl = ⟨"_delegate", .unit⟩ ∧
                                    vt = some (.chan sid r) ∧ R cont q contCand := by
                                simpa [and_left_comm, and_assoc] using hrel
                              rcases hrel' with ⟨h1, h2, h3, h4⟩
                              exact ⟨h1, h2, h3, h _ _ _ h4⟩
                  | cons _ _ =>
                      simpa using hrel
          | _ =>
              simp [CProjectF, hq, hnp] at hrel ⊢
        · simp [CProjectF, hp, hq] at hrel ⊢
          exact h _ _ _ hrel

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
    {partner : String} {lbs : List BranchR}
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
    {partner : String} {lbs : List BranchR}
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
    | delegate _ _ _ _ _ =>
        -- Delegate: follow CProjectF monotonicity pattern
        have : CProjectF S (.delegate _ _ _ _ _) role cand := CProjectF_mono h _ _ _ hcore
        simpa [CProjectF_unfold_core, CProjectF] using this

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

theorem CProject_fixed : CProjectF CProject = CProject := by
  change CProjectF (OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩) =
    OrderHom.gfp ⟨CProjectF, CProjectF_mono⟩
  exact SessionCoTypes.CoinductiveRel.gfp_fixed (F := CProjectF)

theorem CProjectU_fixed : CProjectF_unfold CProjectU = CProjectU := by
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


end Choreography.Projection.Projectb
