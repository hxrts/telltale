import RumpsteakV2.Protocol.Projection.Project.ImplConstructors.Part2

/-! # ImplConstructors Part 3

Mu constructor agreement.
-/

set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.Projection.Project

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.Projection.Trans
open RumpsteakV2.Protocol.Projection.Projectb
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.EQ2Props
open RumpsteakV2.Protocol.CoTypes.EQ2Paco
open Paco
open RumpsteakV2.Protocol.Participation
/-! ### Mu constructor agreement -/

/-- Helper: `.end` cannot project to `.mu`. -/
private theorem CProject_mu_implies_trans_mu_end (role v : String) (body : LocalTypeR)
    (hproj : CProject .end role (.mu v body)) :
    ∃ gbody, trans .end role = .mu v (trans gbody role) ∧
      body.isGuarded v = true ∧
      CProject gbody role body ∧
      gbody.allCommsNonEmpty = true := by
  -- CProjectF forbids .end → .mu.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.var` cannot project to `.mu`. -/
private theorem CProject_mu_implies_trans_mu_var (vt role v : String) (body : LocalTypeR)
    (hproj : CProject (.var vt) role (.mu v body)) :
    ∃ gbody, trans (.var vt) role = .mu v (trans gbody role) ∧
      body.isGuarded v = true ∧
      CProject gbody role body ∧
      gbody.allCommsNonEmpty = true := by
  -- CProjectF forbids .var → .mu.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: mu case for mu projection agreement. -/
private theorem CProject_mu_implies_trans_mu_mu (t : String) (gbody : GlobalType)
    (role v : String) (body : LocalTypeR)
    (hproj : CProject (.mu t gbody) role (.mu v body))
    (hwf : (GlobalType.mu t gbody).allCommsNonEmpty = true) :
    ∃ gbody', trans (.mu t gbody) role = .mu v (trans gbody' role) ∧
      body.isGuarded v = true ∧
      CProject gbody' role body ∧
      gbody'.allCommsNonEmpty = true := by
  -- CProjectF for mu: t = v, body.isGuarded v, CProject gbody role body.
  have hf := CProject_destruct hproj
  simp only [CProjectF] at hf
  rcases hf with ⟨_, hbody_proj, hcase⟩
  rcases hcase with ⟨hguard, hmu_eq⟩ | ⟨_hguard, hend_eq⟩
  · cases hmu_eq
    have hwf_body : gbody.allCommsNonEmpty = true := by
      simpa [GlobalType.allCommsNonEmpty] using hwf
    have htrans_guard : (trans gbody role).isGuarded t = true := by
      simpa using CProject_isGuarded_trans hbody_proj hwf_body hguard
    refine ⟨gbody, ?_, hguard, hbody_proj, hwf_body⟩
    simp [Trans.trans, htrans_guard]
  · have : False := by simpa using hend_eq
    exact this.elim

/-! ### Mu constructor agreement -/

/-- Helper: sender role cannot project to `.mu`. -/
private theorem CProject_mu_implies_trans_mu_comm_sender_contra
    (sender receiver role v : String) (gbs : List (Label × GlobalType)) (body : LocalTypeR)
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (.mu v body))
    (hrs : role = sender) : False := by
  -- CProjectF forbids .mu when the role is sender.
  have hf := CProject_destruct hproj
  simpa [CProjectF, hrs] using hf

/-- Helper: receiver role cannot project to `.mu`. -/
private theorem CProject_mu_implies_trans_mu_comm_receiver_contra
    (sender receiver role v : String) (gbs : List (Label × GlobalType)) (body : LocalTypeR)
    (hproj : CProject (GlobalType.comm sender receiver gbs) role (.mu v body))
    (hrr : role = receiver) (hrs : role ≠ sender) : False := by
  -- CProjectF forbids .mu when the role is receiver.
  have hf := CProject_destruct hproj
  have hns : receiver ≠ sender := by simpa [hrr] using hrs
  simp [CProjectF, hrr, hns] at hf

/-- Helper: non-participant comm case for mu projection agreement. -/
private theorem CProject_mu_implies_trans_mu_comm_other
    (sender receiver role v : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (body : LocalTypeR) (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (hrec :
      ∃ gbody, trans first.2 role = .mu v (trans gbody role) ∧
        body.isGuarded v = true ∧ CProject gbody role body ∧ gbody.allCommsNonEmpty = true) :
    ∃ gbody, trans (GlobalType.comm sender receiver (first :: rest)) role = .mu v (trans gbody role) ∧
      body.isGuarded v = true ∧ CProject gbody role body ∧ gbody.allCommsNonEmpty = true := by
  -- Non-participants use trans_comm_other to select the head branch.
  obtain ⟨gbody, htrans_mu, hguard, hbody_proj, hwf_body⟩ := hrec
  refine ⟨gbody, ?_, hguard, hbody_proj, hwf_body⟩
  have htrans :
      trans (GlobalType.comm sender receiver (first :: rest)) role = trans first.2 role := by
    simpa using trans_comm_other sender receiver role (first :: rest) hrs hrr
  simpa [htrans] using htrans_mu

/- If CProject g role (.mu v body) holds, then trans g role has matching mu structure.
   Returns the global body and proof that trans produces .mu v (trans gbody role). -/
mutual
/-- Helper: comm/cons case for mu projection agreement. -/
private theorem CProject_mu_implies_trans_mu_comm_cons (g : GlobalType) (sender receiver : String)
      (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role v : String)
      (body : LocalTypeR) (hproj : CProject g role (.mu v body))
      (hg : g = (GlobalType.comm sender receiver (first :: rest))) (hne : g.allCommsNonEmpty = true) :
      ∃ gbody, trans (GlobalType.comm sender receiver (first :: rest)) role =
        .mu v (trans gbody role) ∧ body.isGuarded v = true ∧
        CProject gbody role body ∧ gbody.allCommsNonEmpty = true := by
    subst hg -- Non-participant case recurses on the first branch.
    by_cases hrs : role = sender
    · exact (CProject_mu_implies_trans_mu_comm_sender_contra sender receiver role v (first :: rest)
        body hproj hrs).elim
    · by_cases hrr : role = receiver
      · exact (CProject_mu_implies_trans_mu_comm_receiver_contra sender receiver role v (first :: rest)
          body hproj hrr hrs).elim
      · have hf' : AllBranchesProj CProject (first :: rest) role (.mu v body) := by
          simpa [CProjectF, hrs, hrr] using (CProject_destruct hproj)
        have hfirst : CProject first.2 role (.mu v body) :=
          CProject_first_of_AllBranchesProj hf'
        have hne_first : first.2.allCommsNonEmpty = true :=
          allCommsNonEmpty_first_of_comm sender receiver first rest hne
        have hrec := CProject_mu_implies_trans_mu first.2 role v body hfirst hne_first
        exact CProject_mu_implies_trans_mu_comm_other sender receiver role v first rest body hrs hrr hrec
termination_by (sizeOf g) * 3
decreasing_by
    all_goals
      simpa [hg] using sizeOf_snd_lt_comm_head_mul3 sender receiver first rest
/-- Helper: comm case for mu projection agreement. -/
private theorem CProject_mu_implies_trans_mu_comm (sender receiver : String)
      (gbs : List (Label × GlobalType)) (role v : String) (body : LocalTypeR)
      (hproj : CProject (GlobalType.comm sender receiver gbs) role (.mu v body))
      (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true) :
      ∃ gbody, trans (GlobalType.comm sender receiver gbs) role = .mu v (trans gbody role) ∧
        body.isGuarded v = true ∧ CProject gbody role body ∧ gbody.allCommsNonEmpty = true := by
    -- Split on the branch list; empty is impossible under allCommsNonEmpty.
    cases hgb : gbs with
    | nil =>
        have hne' :
            (gbs ≠ [] ∧ GlobalType.allCommsNonEmptyBranches gbs = true) := by
          simpa [GlobalType.allCommsNonEmpty] using hne
        have : False := hne'.1 (by simpa [hgb])
        exact this.elim
    | cons first rest =>
        have hproj' : CProject (GlobalType.comm sender receiver (first :: rest)) role (.mu v body) := by
          simpa [hgb] using hproj
        have hne' : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true := by
          simpa [hgb] using hne
        exact CProject_mu_implies_trans_mu_comm_cons (GlobalType.comm sender receiver (first :: rest))
          sender receiver first rest role v body hproj' rfl hne'
termination_by (sizeOf (GlobalType.comm sender receiver gbs)) * 3 + 1
decreasing_by
    all_goals
      simp [hgb, GlobalType.comm.sizeOf_spec]
/-- If CProject g role (.mu v body) holds, then trans g role has matching mu structure.
      Returns the global body and proof that trans produces `.mu v (trans gbody role)`. -/
theorem CProject_mu_implies_trans_mu (g : GlobalType) (role : String)
      (v : String) (body : LocalTypeR)
      (hproj : CProject g role (.mu v body))
      (hwf : g.allCommsNonEmpty = true) :
      ∃ gbody, trans g role = .mu v (trans gbody role) ∧
        body.isGuarded v = true ∧
        CProject gbody role body ∧
        gbody.allCommsNonEmpty = true := by
    cases hg : g with -- Dispatch by constructor; comm uses the helper above.
    | «end» => exact CProject_mu_implies_trans_mu_end role v body (by simpa [hg] using hproj)
    | var vt => exact CProject_mu_implies_trans_mu_var vt role v body (by simpa [hg] using hproj)
    | mu t gbody =>
        exact CProject_mu_implies_trans_mu_mu t gbody role v body (by simpa [hg] using hproj)
          (by simpa [hg] using hwf)
    | comm sender receiver gbs =>
        simpa [hg] using
          (CProject_mu_implies_trans_mu_comm sender receiver gbs role v body
            (by simpa [hg] using hproj) (by simpa [hg] using hwf))
termination_by (sizeOf g) * 3 + 2
decreasing_by
    all_goals
      simp [hg, GlobalType.comm.sizeOf_spec]
end


end RumpsteakV2.Protocol.Projection.Project
