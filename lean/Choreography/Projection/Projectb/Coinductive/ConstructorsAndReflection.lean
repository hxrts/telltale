import Choreography.Projection.Projectb.Coinductive.Relation

/-! # Coinductive Projection: Constructors and Reflection

Constructor-style lemmas for building and reflecting `CProject` proofs,
enabling case-by-case reasoning about projection relations. -/

/-
The Problem. Building coinductive projection proofs requires unfolding
the fixed-point definition `CProject` for each global type constructor.
Direct `CProjectF`-to-`CProject` coercion is verbose and repetitive.

Solution Structure. Provide constructor theorems (`CProject_end`,
`CProject_var`, `CProject_mu`, `CProject_comm_send`, etc.) that encapsulate
the fixed-point unfolding. Reflection lemmas extract components from
existing `CProject` proofs for use in larger derivations.
-/

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-! ## Constructor Lemmas

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

/-! ## Constructor Lemmas: Communication Cases -/

/-- CProject for comm-send (role is sender). -/
theorem CProject_comm_send (sender receiver : String)
    (gbs : List (Label × GlobalType)) (lbs : List BranchR)
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
    (gbs : List (Label × GlobalType)) (lbs : List BranchR)
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
theorem projectb_end_send (role partner : String) (bs : List BranchR) :
    projectb .end role (.send partner bs) = false := by
  unfold projectb; rfl

/-- Reflection: projectb for end with recv candidate returns false. -/
theorem projectb_end_recv (role partner : String) (bs : List BranchR) :
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
