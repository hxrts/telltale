import Choreography.Projection.Projectb.Coinductive
import SessionTypes.GlobalType.ValType

namespace Choreography.Projection.Projectb

open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-! # Choreography.Projection.Projectb.Typed

Typed projection relation: enriches branch payloads using `PayloadSort.toValType?`.

This is a refinement of projection that checks payload typing on comm branches
while preserving the dedicated delegation payload typing.
-/

/-
The Problem. Basic projection ignores payload types, but runtime execution requires
type-safe message passing. We need a typed projection that verifies payload sorts
convert to valid value types.

Solution Structure. We define:
1. `BranchesProjRelTyped`: branch relation with payload type checking
2. `CProjectF_typed`: one-step generator with typed payloads
3. Monotonicity lemmas for coinductive reasoning
The key insight is that `PayloadSort.toValType?` bridges choreography sorts to session types.
-/

/-- Branch-wise typed projection relation for send/recv. -/
def BranchesProjRelTyped (R : ProjRel)
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR) : Prop :=
  List.Forall₂
    (fun gb lb =>
      gb.1 = lb.1 ∧
        lb.2.1 = PayloadSort.toValType? lb.1.sort ∧
        R gb.2 role lb.2.2)
    gbs lbs

/-! ## Typed Monotonicity Helpers -/

private theorem BranchesProjRelTyped_mono {R S : ProjRel}
    (h : ∀ g r c, R g r c → S g r c) :
    ∀ {gbs lbs role}, BranchesProjRelTyped R gbs role lbs →
      BranchesProjRelTyped S gbs role lbs := by
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

/-! ## Typed Generator -/

/-- One-step generator for typed projection. -/
def CProjectF_typed (R : ProjRel) : ProjRel := fun g role cand =>
  match g, cand with
  | .end, .end => True
  | .var t, .var t' => t = t'
  | .mu t body, cand =>
      ∃ candBody, R body role candBody ∧
        ((candBody.isGuarded t = true ∧ cand = .mu t candBody) ∨
         (candBody.isGuarded t = false ∧ cand = .end))
  | .comm sender receiver gbs, cand =>
      if role = sender then
        match cand with
        | .send partner lbs => partner = receiver ∧ BranchesProjRelTyped R gbs role lbs
        | _ => False
      else if role = receiver then
        match cand with
        | .recv partner lbs => partner = sender ∧ BranchesProjRelTyped R gbs role lbs
        | _ => False
      else
        AllBranchesProj R gbs role cand
  | .delegate p q sid r cont, cand =>
      if role = p then
        match cand with
        | .send partner [(lbl, vt, contCand)] =>
            partner = q ∧
              lbl = ⟨"_delegate", .unit⟩ ∧
              vt = some (.chan sid r) ∧
              R cont role contCand
        | _ => False
      else if role = q then
        match cand with
        | .recv partner [(lbl, vt, contCand)] =>
            partner = p ∧
              lbl = ⟨"_delegate", .unit⟩ ∧
              vt = some (.chan sid r) ∧
              R cont role contCand
        | _ => False
      else
        R cont role cand
  | _, _ => False

/-! ## Typed Generator Monotonicity -/

private theorem CProjectF_typed_mono : Monotone CProjectF_typed := by
  intro R S h g role cand hrel
  cases g with
  | «end» =>
      cases cand <;> simpa [CProjectF_typed] using hrel
  | var t =>
      cases cand <;> simpa [CProjectF_typed] using hrel
  | mu t body =>
      cases cand with
      | mu t' candBody =>
          simp [CProjectF_typed] at hrel ⊢
          rcases hrel with ⟨hbody, hguard, ht⟩
          exact ⟨h _ _ _ hbody, hguard, ht⟩
      | «end» =>
          simp [CProjectF_typed] at hrel ⊢
          rcases hrel with ⟨candBody, hbody, hguard⟩
          exact ⟨candBody, h _ _ _ hbody, hguard⟩
      | var _ =>
          simp [CProjectF_typed] at hrel
      | send _ _ =>
          simp [CProjectF_typed] at hrel
      | recv _ _ =>
          simp [CProjectF_typed] at hrel
  /-! ## CProjectF_typed_mono: Comm Case -/
  | comm sender receiver gbs =>
      by_cases hs : role = sender
      · cases cand with
        | send partner lbs =>
            simp [CProjectF_typed, hs] at hrel ⊢
            rcases hrel with ⟨h1, h2⟩
            exact ⟨h1, BranchesProjRelTyped_mono h h2⟩
        | _ =>
            simp [CProjectF_typed, hs] at hrel ⊢
      · by_cases hr : role = receiver
        · have hns : receiver ≠ sender := by
            intro h
            exact hs (hr.trans h)
          cases cand with
          | recv partner lbs =>
              simp [CProjectF_typed, hr, hns] at hrel ⊢
              rcases hrel with ⟨h1, h2⟩
              exact ⟨h1, BranchesProjRelTyped_mono h h2⟩
          | _ =>
              simp [CProjectF_typed, hr, hns] at hrel ⊢
        · simp [CProjectF_typed, hs, hr] at hrel ⊢
          exact AllBranchesProj_mono h hrel
  /-! ## CProjectF_typed_mono: Delegate Case -/
  | delegate p q sid r cont =>
      by_cases hp : role = p
      · cases cand with
        | send partner lbs =>
            simp [CProjectF_typed, hp] at hrel ⊢
            cases lbs with
            | nil => exact hrel
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
                    exact hrel
        | _ =>
            simp [CProjectF_typed, hp] at hrel ⊢
      /-! ## CProjectF_typed_mono: Delegate Receiver/Other Subcases -/
      · by_cases hq : role = q
        · have hnp : q ≠ p := by
            intro hqp
            exact hp (hq.trans hqp)
          cases cand with
          | recv partner lbs =>
              simp [CProjectF_typed, hq, hnp] at hrel ⊢
              cases lbs with
              | nil => exact hrel
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
                      exact hrel
          | _ =>
              simp [CProjectF_typed, hq, hnp] at hrel ⊢
        · simp [CProjectF_typed, hp, hq] at hrel ⊢
          exact h _ _ _ hrel

/-! ## Coinductive Typed Projection -/

instance : CoinductiveRel ProjRel CProjectF_typed := ⟨CProjectF_typed_mono⟩

/-- Coinductive typed projection relation. -/
def CProjectTyped : ProjRel :=
  (OrderHom.gfp ⟨CProjectF_typed, CProjectF_typed_mono⟩)

/-- Destruct CProjectTyped: if it holds, then CProjectF_typed holds. -/
theorem CProjectTyped_destruct {g : GlobalType} {role : String} {cand : LocalTypeR}
    (h : CProjectTyped g role cand) : CProjectF_typed CProjectTyped g role cand := by
  have hfix : CProjectF_typed CProjectTyped = CProjectTyped := by
    change CProjectF_typed (OrderHom.gfp ⟨CProjectF_typed, CProjectF_typed_mono⟩) =
      OrderHom.gfp ⟨CProjectF_typed, CProjectF_typed_mono⟩
    exact SessionCoTypes.CoinductiveRel.gfp_fixed (F := CProjectF_typed)
  exact Eq.mp (congrArg (fun R => R g role cand) hfix.symm) h

/-! ## Erasure Bridge -/

private def EraseRel : ProjRel := fun g role cand =>
  ∃ cand', CProjectTyped g role cand' ∧ cand = LocalTypeR.eraseValTypes cand'

private theorem BranchesProjRelTyped_to_erase
    {gbs : List (Label × GlobalType)} {role : String} {lbs : List BranchR}
    (h : BranchesProjRelTyped CProjectTyped gbs role lbs) :
    BranchesProjRel EraseRel gbs role (eraseBranchValTypes lbs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hpair hrest ih =>
      rename_i gb lb gbs_tail lbs_tail
      rcases hpair with ⟨hlab, hvt, hproj⟩
      cases lb with
      | mk l rest =>
          cases rest with
          | mk vt cont =>
              have hnone : (match vt with | some (.chan _ _) => vt | _ => none) = none := by
                cases vt with
                | none => rfl
                | some v =>
                    cases v with
                    | chan sid r =>
                        cases l with
                        | mk name sort =>
                            have hvt' : PayloadSort.toValType? sort = some (.chan sid r) := by
                              simpa using hvt.symm
                            exact (False.elim (PayloadSort.toValType?_ne_chan sort sid r hvt'))
                    | unit | bool | nat | string | prod _ _ => rfl
              refine List.Forall₂.cons ?_ ih
              exact ⟨hlab, hnone, ⟨cont, hproj, rfl⟩⟩

private theorem AllBranchesProjTyped_to_erase
    {gbs : List (Label × GlobalType)} {role : String} {cand : LocalTypeR}
    (h : AllBranchesProj CProjectTyped gbs role cand) :
    AllBranchesProj EraseRel gbs role (LocalTypeR.eraseValTypes cand) := by
  intro gb hgb
  exact ⟨cand, h gb hgb, rfl⟩

/-! ## Erasure Bridge: Coinductive Postfix -/

private theorem EraseRel_postfix :
    ∀ g role cand, EraseRel g role cand → CProjectF EraseRel g role cand := by
  intro g role cand hR
  rcases hR with ⟨cand', htyped, rfl⟩
  have hdes := CProjectTyped_destruct htyped
  cases g with
  | «end» =>
      cases cand' <;> simpa [CProjectF_typed, CProjectF, LocalTypeR.eraseValTypes] using hdes
  | var t =>
      cases cand' <;> simpa [CProjectF_typed, CProjectF, LocalTypeR.eraseValTypes] using hdes
  | mu t body =>
      cases cand' with
      | mu t' candBody =>
          simp [CProjectF_typed] at hdes
          rcases hdes with ⟨hbody, hguard, ht⟩
          subst ht
          refine ⟨LocalTypeR.eraseValTypes candBody, ⟨candBody, hbody, rfl⟩, ?_⟩
          left
          exact ⟨by simpa using hguard, rfl⟩
      | «end» =>
          simp [CProjectF_typed] at hdes
          rcases hdes with ⟨candBody, hbody, hguard⟩
          refine ⟨LocalTypeR.eraseValTypes candBody, ⟨candBody, hbody, rfl⟩, ?_⟩
          right
          exact ⟨by simpa using hguard, rfl⟩
      | var _ =>
          simp [CProjectF_typed] at hdes
      | send _ _ =>
          simp [CProjectF_typed] at hdes
      | recv _ _ =>
          simp [CProjectF_typed] at hdes
  /-! ## Erasure Bridge: Comm Case -/
  | comm sender receiver gbs =>
      by_cases hs : role = sender
      · cases cand' with
        | send partner lbs =>
            simp [CProjectF_typed, hs] at hdes
            rcases hdes with ⟨hpartner, hbranches⟩
            have hbranches_role : BranchesProjRelTyped CProjectTyped gbs role lbs := by
              simpa [hs] using hbranches
            have hbranches' :
                BranchesProjRel EraseRel gbs role (eraseBranchValTypes lbs) :=
              BranchesProjRelTyped_to_erase hbranches_role
            simpa [CProjectF, hs, LocalTypeR.eraseValTypes] using
              And.intro hpartner hbranches'
        | _ =>
            simp [CProjectF_typed, hs] at hdes
      /-! ## Erasure Bridge: Comm Receiver/Other Subcases -/
      · by_cases hr : role = receiver
        · have hns : receiver ≠ sender := by
            intro h
            exact hs (hr.trans h)
          cases cand' with
          | recv partner lbs =>
              simp [CProjectF_typed, hr, hns] at hdes
              rcases hdes with ⟨hpartner, hbranches⟩
              have hbranches_role : BranchesProjRelTyped CProjectTyped gbs role lbs := by
                simpa [hr] using hbranches
              have hbranches' :
                  BranchesProjRel EraseRel gbs role (eraseBranchValTypes lbs) :=
                BranchesProjRelTyped_to_erase hbranches_role
              simpa [CProjectF, hs, hr, hns, LocalTypeR.eraseValTypes] using
                And.intro hpartner hbranches'
          | _ =>
              simp [CProjectF_typed, hr, hns] at hdes
        · simp [CProjectF_typed, hs, hr] at hdes
          have hbranches' :
              AllBranchesProj EraseRel gbs role (LocalTypeR.eraseValTypes cand') :=
            AllBranchesProjTyped_to_erase hdes
          simpa [CProjectF, hs, hr, LocalTypeR.eraseValTypes] using hbranches'
  /-! ## Erasure Bridge: Delegate Case -/
  | delegate p q sid r cont =>
      by_cases hp : role = p
      · cases cand' with
        | send partner lbs =>
            simp [CProjectF_typed, hp] at hdes
            cases lbs with
            | nil =>
                simpa [CProjectF, hp, LocalTypeR.eraseValTypes] using hdes
            | cons b bs =>
                cases bs with
                | nil =>
                    cases b with
                    | mk lbl rest =>
                        cases rest with
                        | mk vt contCand =>
                            have hrel' :
                                partner = q ∧ lbl = ⟨"_delegate", .unit⟩ ∧
                                  vt = some (.chan sid r) ∧ CProjectTyped cont role contCand := by
                              simpa [hp, and_left_comm, and_assoc] using hdes
                            rcases hrel' with ⟨h1, h2, h3, h4⟩
                            have h4' : EraseRel cont role (LocalTypeR.eraseValTypes contCand) :=
                              ⟨contCand, h4, rfl⟩
                            simpa [CProjectF, hp, LocalTypeR.eraseValTypes, eraseBranchValTypes,
                              h1, h2, h3] using
                              And.intro h1 (And.intro h2 (And.intro h3 h4'))
                | cons _ _ =>
                    simpa [CProjectF, hp, LocalTypeR.eraseValTypes] using hdes
        | _ =>
            simp [CProjectF_typed, hp] at hdes
      /-! ## Erasure Bridge: Delegate Receiver/Other Subcases -/
      · by_cases hq : role = q
        · have hnp : q ≠ p := by
            intro hqp
            exact hp (hq.trans hqp)
          cases cand' with
          | recv partner lbs =>
              simp [CProjectF_typed, hq, hnp] at hdes
              cases lbs with
              | nil =>
                  simpa [CProjectF, hp, hq, hnp, LocalTypeR.eraseValTypes] using hdes
              | cons b bs =>
                  cases bs with
                  | nil =>
                      cases b with
                      | mk lbl rest =>
                          cases rest with
                          | mk vt contCand =>
                              have hrel' :
                                  partner = p ∧ lbl = ⟨"_delegate", .unit⟩ ∧
                                    vt = some (.chan sid r) ∧ CProjectTyped cont role contCand := by
                                simpa [hq, and_left_comm, and_assoc] using hdes
                              rcases hrel' with ⟨h1, h2, h3, h4⟩
                              have h4' : EraseRel cont role (LocalTypeR.eraseValTypes contCand) :=
                                ⟨contCand, h4, rfl⟩
                              simpa [CProjectF, hp, hq, hnp, LocalTypeR.eraseValTypes,
                                eraseBranchValTypes, h1, h2, h3] using
                                And.intro h1 (And.intro h2 (And.intro h3 h4'))
                  | cons _ _ =>
                      simpa [CProjectF, hp, hq, hnp, LocalTypeR.eraseValTypes] using hdes
          | _ =>
              have hfalse : False := by
                simpa [CProjectF_typed, hq, hnp] using hdes
              simpa [CProjectF, hp, hq, hnp, LocalTypeR.eraseValTypes] using hfalse
        · simp [CProjectF_typed, CProjectF, hp, hq] at hdes ⊢
          exact ⟨_, hdes, rfl⟩

/-! ## Typed-to-Erased Theorem -/

/-- Typed projection implies erased projection on the payload-erased candidate. -/
theorem CProjectTyped_implies_CProject_erase
    {g : GlobalType} {role : String} {cand : LocalTypeR}
    (h : CProjectTyped g role cand) :
    CProject g role (LocalTypeR.eraseValTypes cand) := by
  have hrel : EraseRel g role (LocalTypeR.eraseValTypes cand) := ⟨cand, h, rfl⟩
  exact CProject_coind EraseRel_postfix g role _ hrel

end Choreography.Projection.Projectb
