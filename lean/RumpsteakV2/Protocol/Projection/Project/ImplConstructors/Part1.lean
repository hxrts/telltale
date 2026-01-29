import RumpsteakV2.Protocol.Projection.Project.ImplBase

/-! # ImplConstructors Part 1

Constructor agreement for end, var, and send/recv structural extraction.
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

/-! ### Constructor Agreement Lemmas (Well-Founded Induction)

These lemmas prove that when CProject produces a specific constructor (.end, .var),
trans also produces that same constructor. Proved by well-founded induction on the
global type size, NOT using the coinductive theorem.

This breaks the circularity: CProjectTransRel_postfix needs to know that trans produces
the same constructor as CProject, but CProject_implies_EQ2_trans depends on CProjectTransRel_postfix. -/

/-- Helper: extract projection of the first branch from AllBranchesProj. -/
theorem CProject_first_of_AllBranchesProj {first : Label × GlobalType}
    {rest : List (Label × GlobalType)} {role : String} {lt : LocalTypeR}
    (hf : AllBranchesProj CProject (first :: rest) role lt) : CProject first.2 role lt := by
  -- The head branch is always a member of the list.
  exact hf first (by simp)

/-- Helper: first branch inherits allCommsNonEmpty from a non-empty comm. -/
theorem allCommsNonEmpty_first_of_comm (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (hne : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true) :
    first.2.allCommsNonEmpty = true := by
  -- Use the comm-branches lemma and pick the head.
  have hne_branches :
      ∀ gb ∈ (first :: rest), gb.2.allCommsNonEmpty = true := by
    simpa using GlobalType.allCommsNonEmpty_comm_branches _ _ (first :: rest) hne
  exact hne_branches first (by simp)

/-- Helper: wellFormed implies allCommsNonEmpty. -/
theorem allCommsNonEmpty_of_wellFormed (g : GlobalType)
    (hwf : g.wellFormed = true) : g.allCommsNonEmpty = true := by
  -- Unpack wellFormed to reach allCommsNonEmpty.
  have hwf' := hwf
  simp [GlobalType.wellFormed, Bool.and_eq_true] at hwf'
  exact hwf'.1.1.2

/-- Helper: first branch inherits wellFormed from a non-empty comm. -/
theorem wellFormed_first_of_comm (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (hwf : (GlobalType.comm sender receiver (first :: rest)).wellFormed = true) :
    first.2.wellFormed = true := by
  -- Use the comm-branches lemma and pick the head.
  have hwf_branches :
      ∀ gb ∈ (first :: rest), gb.2.wellFormed = true := by
    exact GlobalType.wellFormed_comm_branches sender receiver (first :: rest) hwf
  exact hwf_branches first (by simp)

/-- Helper: size decreases from a comm node to any branch continuation. -/
private theorem sizeOf_snd_lt_comm_of_mem (sender receiver : String)
    {branches : List (Label × GlobalType)} {p : Label × GlobalType} (hp : p ∈ branches) :
    sizeOf p.2 < sizeOf (GlobalType.comm sender receiver branches) := by
  have h1 : sizeOf p.2 < sizeOf p := by
    cases p with
    | mk l g => simp; omega
  have h2 : sizeOf p < 1 + sizeOf branches := by
    have := List.sizeOf_lt_of_mem hp
    omega
  have h3 : 1 + sizeOf branches < sizeOf (GlobalType.comm sender receiver branches) := by
    simp [GlobalType.comm.sizeOf_spec]
    have hs : 0 < sizeOf sender := by
      have : sizeOf sender = 1 + sizeOf sender.bytes + sizeOf sender.isValidUTF8 := rfl
      omega
    have hr : 0 < sizeOf receiver := by
      have : sizeOf receiver = 1 + sizeOf receiver.bytes + sizeOf receiver.isValidUTF8 := rfl
      omega
    omega
  exact Nat.lt_trans h1 (Nat.lt_trans h2 h3)

/-- Helper: size decreases from a comm node to the head branch. -/
private theorem sizeOf_snd_lt_comm_head (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf first.2 < sizeOf (GlobalType.comm sender receiver (first :: rest)) := by
  exact sizeOf_snd_lt_comm_of_mem sender receiver (by simp)

/-- Helper: size decreases for mutual recursion measure (comm → branch). -/
private theorem sizeOf_snd_lt_comm_head_mul (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf first.2 * 2 + 1 < sizeOf (GlobalType.comm sender receiver (first :: rest)) * 2 := by
  have hlt := sizeOf_snd_lt_comm_head sender receiver first rest
  omega

theorem sizeOf_snd_lt_comm_head_mul3 (sender receiver : String)
    (first : Label × GlobalType) (rest : List (Label × GlobalType)) :
    sizeOf first.2 * 3 + 2 < sizeOf (GlobalType.comm sender receiver (first :: rest)) * 3 := by
  have hlt := sizeOf_snd_lt_comm_head sender receiver first rest
  omega


/-! ### End constructor agreement -/

/-- Helper: `.end` case is definitional. -/
private theorem CProject_end_trans_end_end (role : String)
    (_ : CProject .end role .end) : trans .end role = .end := by
  -- Base case: trans .end is definitionally .end.
  simp [Trans.trans]

/-- Helper: `.var` cannot project to `.end`. -/
private theorem CProject_end_trans_end_var (v : String) (role : String)
    (h : CProject (.var v) role .end) : trans (.var v) role = .end := by
  -- CProjectF cannot relate .var to .end.
  have hf := CProject_destruct h
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.mu` case reduces to unguarded body. -/
private theorem CProject_end_trans_end_mu (t : String) (body : GlobalType) (role : String)
    (h : CProject (.mu t body) role .end) (hne : (GlobalType.mu t body).allCommsNonEmpty = true) :
    trans (.mu t body) role = .end := by
  -- Use the mu/end branch of CProjectF to show the body is unguarded.
  have hf := CProject_destruct h
  simp [CProjectF] at hf
  rcases hf with ⟨candBody, hbody, hguard⟩
  have hne_body : body.allCommsNonEmpty = true := by
    simpa [GlobalType.allCommsNonEmpty] using hne
  -- The .end candidate forces the unguarded branch.
  have htrans_guard : (trans body role).isGuarded t = false :=
    CProject_unguarded_trans hbody hne_body hguard
  simp [Trans.trans, htrans_guard]

/-- Helper: sender role cannot project a comm to .end. -/
private theorem CProject_end_trans_end_comm_sender_contra
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (h : CProject (.comm sender receiver branches) role .end)
    (hrs : role = sender) : False := by
  -- CProjectF forbids .end when the role is sender.
  have hf := CProject_destruct h
  simpa [CProjectF, hrs] using hf

/-- Helper: receiver role cannot project a comm to .end. -/
private theorem CProject_end_trans_end_comm_receiver_contra
    (sender receiver role : String) (branches : List (Label × GlobalType))
    (h : CProject (.comm sender receiver branches) role .end)
    (hrr : role = receiver) (hrs : role ≠ sender) : False := by
  -- CProjectF forbids .end when the role is receiver.
  have hf := CProject_destruct h
  have hns : receiver ≠ sender := by simpa [hrr] using hrs
  simp [CProjectF, hrr, hns] at hf

/-- Helper: non-participant comm case reduces to the head branch. -/
private theorem CProject_end_trans_end_comm_other
    (sender receiver role : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (ih : trans first.2 role = .end) :
    trans (.comm sender receiver (first :: rest)) role = .end := by
  -- Non-participants use trans_comm_other to select the head branch.
  have htrans :
      trans (.comm sender receiver (first :: rest)) role = trans first.2 role := by
    simpa using trans_comm_other sender receiver role (first :: rest) hrs hrr
  exact htrans.trans ih

mutual
/-- Helper: comm/cons case for end projection agreement. -/
private theorem CProject_end_trans_end_comm_cons (g : GlobalType) (sender receiver : String)
      (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role : String)
      (h : CProject g role .end)
      (hg : g = (GlobalType.comm sender receiver (first :: rest)))
      (hne : g.allCommsNonEmpty = true) :
      trans (GlobalType.comm sender receiver (first :: rest)) role = .end := by
    subst hg
    -- Non-participant case recurses on the first branch.
    by_cases hrs : role = sender
    · exact (CProject_end_trans_end_comm_sender_contra sender receiver role (first :: rest) h hrs).elim
    · by_cases hrr : role = receiver
      · exact (CProject_end_trans_end_comm_receiver_contra sender receiver role (first :: rest)
          h hrr hrs).elim
      · have hf : AllBranchesProj CProject (first :: rest) role .end := by
          simpa [CProjectF, hrs, hrr] using (CProject_destruct h)
        have hfirst : CProject first.2 role .end :=
          CProject_first_of_AllBranchesProj hf
        have hne_first : first.2.allCommsNonEmpty = true :=
          allCommsNonEmpty_first_of_comm sender receiver first rest hne
        have ih := CProject_end_trans_end first.2 role hfirst hne_first
        exact CProject_end_trans_end_comm_other sender receiver role first rest hrs hrr ih
termination_by (sizeOf g) * 3
decreasing_by
    all_goals
      simpa [hg] using sizeOf_snd_lt_comm_head_mul3 sender receiver first rest

/-- Helper: comm case for end projection agreement. -/
private theorem CProject_end_trans_end_comm (sender receiver : String)
      (gbs : List (Label × GlobalType)) (role : String)
      (h : CProject (.comm sender receiver gbs) role .end)
      (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true) :
      trans (.comm sender receiver gbs) role = .end := by
    -- Split on the branch list; empty is impossible under allCommsNonEmpty.
    cases hgb : gbs with
    | nil =>
        have hne' :
            (gbs ≠ [] ∧ GlobalType.allCommsNonEmptyBranches gbs = true) := by
          simpa [GlobalType.allCommsNonEmpty] using hne
        have : False := hne'.1 (by simpa [hgb])
        exact this.elim
    | cons first rest =>
        have h' : CProject (.comm sender receiver (first :: rest)) role .end := by
          simpa [hgb] using h
        have hne' : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true := by
          simpa [hgb] using hne
        exact CProject_end_trans_end_comm_cons (.comm sender receiver (first :: rest))
          sender receiver first rest role h' rfl hne'
termination_by (sizeOf (GlobalType.comm sender receiver gbs)) * 3 + 1
decreasing_by
    all_goals
      simp [hgb, GlobalType.comm.sizeOf_spec]

/-- If CProject g role .end, then trans g role = .end.
      Proved by well-founded induction on g. -/
theorem CProject_end_trans_end (g : GlobalType) (role : String)
      (h : CProject g role .end) (hne : g.allCommsNonEmpty = true) :
      trans g role = .end := by
    -- Dispatch by constructor; comm uses the helper above.
    cases hg : g with
    | «end» =>
        exact CProject_end_trans_end_end role (by simpa [hg] using h)
    | var v =>
        exact CProject_end_trans_end_var v role (by simpa [hg] using h)
    | mu t body =>
        exact CProject_end_trans_end_mu t body role
          (by simpa [hg] using h) (by simpa [hg] using hne)
    | comm sender receiver gbs =>
        simpa [hg] using
          (CProject_end_trans_end_comm sender receiver gbs role
            (by simpa [hg] using h) (by simpa [hg] using hne))
termination_by (sizeOf g) * 3 + 2
decreasing_by
    all_goals
      simp [hg, GlobalType.comm.sizeOf_spec]
end

/-! ### Var constructor agreement -/

/-- Helper: `.end` cannot project to `.var`. -/
private theorem CProject_var_trans_var_end (role v : String)
    (h : CProject .end role (.var v)) : trans .end role = .var v := by
  -- CProjectF forbids .end → .var.
  have hf := CProject_destruct h
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.var` projects to itself. -/
private theorem CProject_var_trans_var_var (v v' role : String)
    (h : CProject (.var v') role (.var v)) : trans (.var v') role = .var v := by
  -- CProjectF forces v' = v, then trans is definitional.
  have hf := CProject_destruct h
  simp [CProjectF] at hf
  simpa [Trans.trans, hf]

/-- Helper: `.mu` cannot project to `.var`. -/
private theorem CProject_var_trans_var_mu (t : String) (body : GlobalType) (role v : String)
    (h : CProject (.mu t body) role (.var v)) : trans (.mu t body) role = .var v := by
  -- CProjectF forbids .mu → .var.
  have hf := CProject_destruct h
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: sender role cannot project a comm to `.var`. -/
private theorem CProject_var_trans_var_comm_sender_contra
    (sender receiver role v : String) (branches : List (Label × GlobalType))
    (h : CProject (.comm sender receiver branches) role (.var v))
    (hrs : role = sender) : False := by
  -- CProjectF forbids .var when the role is sender.
  have hf := CProject_destruct h
  simpa [CProjectF, hrs] using hf

/-- Helper: receiver role cannot project a comm to `.var`. -/
private theorem CProject_var_trans_var_comm_receiver_contra
    (sender receiver role v : String) (branches : List (Label × GlobalType))
    (h : CProject (.comm sender receiver branches) role (.var v))
    (hrr : role = receiver) (hrs : role ≠ sender) : False := by
  -- CProjectF forbids .var when the role is receiver.
  have hf := CProject_destruct h
  have hns : receiver ≠ sender := by simpa [hrr] using hrs
  simp [CProjectF, hrr, hns] at hf

/-- Helper: non-participant comm case reduces to the head branch. -/
private theorem CProject_var_trans_var_comm_other
    (sender receiver role v : String) (first : Label × GlobalType) (rest : List (Label × GlobalType))
    (hrs : role ≠ sender) (hrr : role ≠ receiver)
    (ih : trans first.2 role = .var v) :
    trans (.comm sender receiver (first :: rest)) role = .var v := by
  -- Non-participants use trans_comm_other to select the head branch.
  have htrans :
      trans (.comm sender receiver (first :: rest)) role = trans first.2 role := by
    simpa using trans_comm_other sender receiver role (first :: rest) hrs hrr
  exact htrans.trans ih

mutual
/-- Helper: comm/cons case for var projection agreement. -/
private theorem CProject_var_trans_var_comm_cons (g : GlobalType) (sender receiver : String)
      (first : Label × GlobalType) (rest : List (Label × GlobalType)) (role v : String)
      (h : CProject g role (.var v))
      (hg : g = (GlobalType.comm sender receiver (first :: rest)))
      (hne : g.allCommsNonEmpty = true) :
      trans (GlobalType.comm sender receiver (first :: rest)) role = .var v := by
    subst hg
    -- Non-participant case recurses on the first branch.
    by_cases hrs : role = sender
    · exact (CProject_var_trans_var_comm_sender_contra sender receiver role v (first :: rest) h
        hrs).elim
    · by_cases hrr : role = receiver
      · exact (CProject_var_trans_var_comm_receiver_contra sender receiver role v (first :: rest)
          h hrr hrs).elim
      · have hf : AllBranchesProj CProject (first :: rest) role (.var v) := by
          simpa [CProjectF, hrs, hrr] using (CProject_destruct h)
        have hfirst : CProject first.2 role (.var v) :=
          CProject_first_of_AllBranchesProj hf
        have hne_first : first.2.allCommsNonEmpty = true :=
          allCommsNonEmpty_first_of_comm sender receiver first rest hne
        have ih := CProject_var_trans_var first.2 role v hfirst hne_first
        exact CProject_var_trans_var_comm_other sender receiver role v first rest hrs hrr ih
termination_by (sizeOf g) * 3
decreasing_by
    all_goals
      simpa [hg] using sizeOf_snd_lt_comm_head_mul3 sender receiver first rest

/-- Helper: comm case for var projection agreement. -/
private theorem CProject_var_trans_var_comm (sender receiver : String)
      (gbs : List (Label × GlobalType)) (role v : String)
      (h : CProject (.comm sender receiver gbs) role (.var v))
      (hne : (GlobalType.comm sender receiver gbs).allCommsNonEmpty = true) :
      trans (.comm sender receiver gbs) role = .var v := by
    -- Split on the branch list; empty is impossible under allCommsNonEmpty.
    cases hgb : gbs with
    | nil =>
        have hne' :
            (gbs ≠ [] ∧ GlobalType.allCommsNonEmptyBranches gbs = true) := by
          simpa [GlobalType.allCommsNonEmpty] using hne
        have : False := hne'.1 (by simpa [hgb])
        exact this.elim
    | cons first rest =>
        have h' : CProject (.comm sender receiver (first :: rest)) role (.var v) := by
          simpa [hgb] using h
        have hne' : (GlobalType.comm sender receiver (first :: rest)).allCommsNonEmpty = true := by
          simpa [hgb] using hne
        exact CProject_var_trans_var_comm_cons (.comm sender receiver (first :: rest))
          sender receiver first rest role v h' rfl hne'
termination_by (sizeOf (GlobalType.comm sender receiver gbs)) * 3 + 1
decreasing_by
    all_goals
      simp [hgb, GlobalType.comm.sizeOf_spec]

/-- If CProject g role (.var v) and g has non-empty branches, then trans g role = .var v.
      Proved by well-founded induction on g.
      The allCommsNonEmpty precondition ensures branches are non-empty. -/
theorem CProject_var_trans_var (g : GlobalType) (role : String) (v : String)
      (h : CProject g role (.var v)) (hwf : g.allCommsNonEmpty = true) :
      trans g role = .var v := by
    -- Dispatch by constructor; comm uses the helper above.
    cases hg : g with
    | «end» =>
        exact CProject_var_trans_var_end role v (by simpa [hg] using h)
    | var v' =>
        exact CProject_var_trans_var_var v v' role (by simpa [hg] using h)
    | mu t body =>
        exact CProject_var_trans_var_mu t body role v (by simpa [hg] using h)
    | comm sender receiver gbs =>
        simpa [hg] using
          (CProject_var_trans_var_comm sender receiver gbs role v
            (by simpa [hg] using h) (by simpa [hg] using hwf))
termination_by (sizeOf g) * 3 + 2
decreasing_by
    all_goals
      simp [hg, GlobalType.comm.sizeOf_spec]
end

/-! ### CProject-to-Trans structure extraction

When CProject produces a specific local type constructor (.send, .recv, .end, .var, .mu),
the global type must have a corresponding structure. These lemmas extract that structure
and show trans produces the matching constructor. -/

/-- Helper: `.end` cannot project to `.send`. -/
theorem CProject_send_implies_trans_send_end (role partner : String)
    (lbs : List (Label × LocalTypeR))
    (hproj : CProject .end role (.send partner lbs)) :
    ∃ gbs', trans .end role = .send partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- CProjectF forbids .end → .send.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.var` cannot project to `.send`. -/
theorem CProject_send_implies_trans_send_var (v role partner : String)
    (lbs : List (Label × LocalTypeR))
    (hproj : CProject (.var v) role (.send partner lbs)) :
    ∃ gbs', trans (.var v) role = .send partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- CProjectF forbids .var → .send.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

/-- Helper: `.mu` cannot project to `.send`. -/
theorem CProject_send_implies_trans_send_mu (t : String) (body : GlobalType)
    (role partner : String) (lbs : List (Label × LocalTypeR))
    (hproj : CProject (.mu t body) role (.send partner lbs)) :
    ∃ gbs', trans (.mu t body) role = .send partner (transBranches gbs' role) ∧
      BranchesProjRel CProject gbs' role lbs ∧
      (∀ gb, gb ∈ gbs' → gb.2.wellFormed = true) := by
  -- CProjectF forbids .mu → .send.
  have hf := CProject_destruct hproj
  have : False := by simpa [CProjectF] using hf
  exact this.elim

end RumpsteakV2.Protocol.Projection.Project
