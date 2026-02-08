import Choreography.Projection.Projectb.Coinductive

namespace Choreography.Projection.Projectb
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
open SessionTypes.Participation
open SessionCoTypes.CoinductiveRel

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-! # Choreography.Projection.Projectb.Soundness

Soundness and completeness of `projectb` with respect to `CProject`.
-/

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
  | real => cases b <;> simp_all [reduceBEq]
  | vector n =>
      cases b with
      | vector m =>
          simp only [reduceBEq, beq_iff_eq] at h
          simp only [h]
      | _ => simp_all [reduceBEq]
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

/-- Helper: ValType BEq true implies equality (avoid LawfulBEq instance). -/
private theorem valType_beq_eq_true_to_eq
    {a b : SessionTypes.ValType} (h : (a == b) = true) : a = b := by
  induction a generalizing b with
  | unit =>
      cases b with
      | unit => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | bool =>
      cases b with
      | bool => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | nat =>
      cases b with
      | nat => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | string =>
      cases b with
      | string => rfl
      | _ =>
          have : False := by simpa [reduceBEq] using h
          exact this.elim
  | prod a1 a2 ih1 ih2 =>
      cases b with
      | prod b1 b2 =>
          simp [reduceBEq, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          have ha1 : a1 = b1 := ih1 h1
          have ha2 : a2 = b2 := ih2 h2
          simp [ha1, ha2]
      | _ =>
          simp [reduceBEq] at h
  | chan sid r =>
      cases b with
      | chan sid' r' =>
          simp [reduceBEq, Bool.and_eq_true] at h
          obtain ⟨hsid, hr⟩ := h
          have hsid' : sid = sid' := by simpa using hsid
          have hr' : r = r' := by simpa using hr
          simp [hsid', hr']
      | _ =>
          simp [reduceBEq] at h

/-- Helper: Option ValType BEq true implies equality (avoid LawfulBEq instance). -/
private theorem optionValType_beq_eq_true_to_eq
    {a b : Option SessionTypes.ValType} (h : (a == b) = true) : a = b := by
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some _ =>
          have hfalse : False := by
            simpa using h
          exact hfalse.elim
  | some a =>
      cases b with
      | none =>
          have hfalse : False := by
            simpa using h
          exact hfalse.elim
      | some b =>
          have h' : (a == b) = true := by simpa using h
          have hab : a = b := valType_beq_eq_true_to_eq h'
          simp [hab]

/-- Helper: PayloadSort beq is reflexive. -/
private theorem payloadSort_beq_refl (s : PayloadSort) : (s == s) = true := by
  induction s with
  | unit => rfl
  | nat => rfl
  | bool => rfl
  | string => rfl
  | real => rfl
  | vector n => simp only [reduceBEq, beq_self_eq_true]
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
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR)
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
          split_ifs at h with hlabel hnone
          -- Only one goal: both tests must succeed to get true.
          have ⟨hproj, hrest⟩ := bool_and_true h
          have hlabel' : ghd.1 = lhd.1 := label_beq_eq_true_to_eq hlabel
          have hnone' : lhd.2.1 = none := by
            cases lhd with
            | mk lbl rest =>
                cases rest with
                | mk vt cont =>
                    cases vt with
                    | none => rfl
                    | some t =>
                        cases (Bool.false_ne_true hnone)
          exact List.Forall₂.cons ⟨hlabel', hnone', hproj⟩ (ih ltl hrest)

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

/-! ### SoundRel Postfix Helpers -/

/-- SoundRel postfix: end case. -/
private theorem SoundRel_postfix_end (role : String) (cand : LocalTypeR)
    (h : SoundRel .end role cand) : CProjectF SoundRel .end role cand := by
  -- Reduce to the projectb definition for end.
  cases cand <;> simp [SoundRel, projectb, CProjectF] at h ⊢

/-- SoundRel postfix: var case. -/
private theorem SoundRel_postfix_var (t : String) (role : String) (cand : LocalTypeR)
    (h : SoundRel (.var t) role cand) : CProjectF SoundRel (.var t) role cand := by
  -- Extract equality from projectb for the var/var case; other cases contradict.
  cases cand with
  | var t' =>
      have ht : (t == t') = true := by
        simpa [SoundRel, projectb] using h
      exact string_beq_eq_true_to_eq ht
  | «end» =>
      simp [SoundRel, projectb] at h
  | send _ _ =>
      simp [SoundRel, projectb] at h
  | recv _ _ =>
      simp [SoundRel, projectb] at h
  | mu _ _ =>
      simp [SoundRel, projectb] at h

/-- SoundRel postfix: mu case with `.end` candidate. -/
private theorem SoundRel_postfix_mu_end (t : String) (body : GlobalType) (role : String)
    (h : SoundRel (.mu t body) role .end) : CProjectF SoundRel (.mu t body) role .end := by
  -- Extract the projected body witness from the projectb branch.
  simp [SoundRel, projectb] at h
  set candBody := Trans.trans body role with hcandBody
  by_cases hguard : candBody.isGuarded t = true
  · -- Guarded body contradicts projectb = true in the `.end` case.
    simp [hguard] at h
  · -- Unguarded body provides the SoundRel witness.
    have hbody : SoundRel body role candBody := by
      simpa [SoundRel, hguard] using h
    exact ⟨candBody, hbody, Or.inr ⟨by simp [hguard], rfl⟩⟩

/-- SoundRel postfix: mu case with `.mu` candidate. -/
private theorem SoundRel_postfix_mu_mu
    (t t' : String) (body : GlobalType) (candBody : LocalTypeR) (role : String)
    (h : SoundRel (.mu t body) role (.mu t' candBody)) :
    CProjectF SoundRel (.mu t body) role (.mu t' candBody) := by
  -- Unpack the guardedness check and the recursive SoundRel hypothesis.
  by_cases ht : (t == t') = true
  · dsimp [SoundRel] at h
    simp [projectb, ht] at h
    by_cases hguard : candBody.isGuarded t' = true
    · simp [hguard] at h
      have hbody : SoundRel body role candBody := h
      have ht' : t = t' := string_beq_eq_true_to_eq ht
      subst ht'
      exact ⟨candBody, hbody, Or.inl ⟨by simp [hguard], rfl⟩⟩
    · have hfalse : False := by
        simp [hguard] at h
      exact hfalse.elim
  · dsimp [SoundRel] at h
    have hfalse : False := by
      simp [projectb, ht] at h
    exact hfalse.elim

/-- SoundRel postfix: mu case for non-mu candidates. -/
private theorem SoundRel_postfix_mu_other
    (t : String) (body : GlobalType) (role : String) (cand : LocalTypeR)
    (h : SoundRel (.mu t body) role cand)
    (hneq : cand ≠ .end) (hneq' : ∀ t' body', cand ≠ .mu t' body') :
    False := by
  -- All non-end, non-mu candidates force projectb = false.
  cases cand <;> simp [SoundRel, projectb] at h
  · exact hneq rfl
  · exact hneq' _ _ rfl

/-- SoundRel postfix: mu case dispatcher. -/
private theorem SoundRel_postfix_mu (t : String) (body : GlobalType) (role : String)
    (cand : LocalTypeR) (h : SoundRel (.mu t body) role cand) :
    CProjectF SoundRel (.mu t body) role cand := by
  -- Split on the candidate shape to select the appropriate helper.
  cases cand with
  | «end» => exact SoundRel_postfix_mu_end t body role h
  | mu t' candBody => exact SoundRel_postfix_mu_mu t t' body candBody role h
  | var v =>
      have hfalse := SoundRel_postfix_mu_other t body role (.var v) h (by simp) (by intro; simp)
      exact (False.elim hfalse)
  | send p bs =>
      have hfalse := SoundRel_postfix_mu_other t body role (.send p bs) h (by simp) (by intro; simp)
      exact (False.elim hfalse)
  | recv p bs =>
      have hfalse := SoundRel_postfix_mu_other t body role (.recv p bs) h (by simp) (by intro; simp)
      exact (False.elim hfalse)

/-- Helper: sender comm case when candidate is a send. -/
private theorem SoundRel_postfix_comm_sender_send
    (sender receiver role : String) (gbs : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR) (hs : role = sender)
    (h : SoundRel (.comm sender receiver gbs) role (.send partner lbs)) :
    CProjectF SoundRel (.comm sender receiver gbs) role (.send partner lbs) := by
  -- Reduce to the branch checker and convert it into a BranchesProjRel witness.
  have h' :
      (if partner == receiver then projectbBranches gbs role lbs else false) = true := by
    simpa [SoundRel, projectb, hs] using h
  by_cases hpartner : (partner == receiver) = true
  · have hbranches : projectbBranches gbs role lbs = true := by
      simpa [hpartner] using h'
    have hbranches' : BranchesProjRel SoundRel gbs sender lbs := by
      simpa [hs] using projectbBranches_to_SoundRel gbs role lbs hbranches
    have hpartner_eq : partner = receiver := string_beq_eq_true_to_eq hpartner
    simpa [CProjectF, hs] using ⟨hpartner_eq, hbranches'⟩
  · have hfalse : False := by
      simp [hpartner] at h'
    exact hfalse.elim

/-- SoundRel postfix: comm case for sender role. -/
private theorem SoundRel_postfix_comm_sender
    (sender receiver role : String) (gbs : List (Label × GlobalType))
    (cand : LocalTypeR) (hs : role = sender)
    (h : SoundRel (.comm sender receiver gbs) role cand) :
    CProjectF SoundRel (.comm sender receiver gbs) role cand := by
  -- Sender projections must be sends with matching partner and projected branches.
  cases cand with
  | send partner lbs =>
      -- Delegate to the specialized send-case helper.
      exact SoundRel_postfix_comm_sender_send sender receiver role gbs partner lbs hs h
  | «end» =>
      simp [SoundRel, projectb, hs] at h
  | var _ =>
      simp [SoundRel, projectb, hs] at h
  | recv _ _ =>
      simp [SoundRel, projectb, hs] at h
  | mu _ _ =>
      simp [SoundRel, projectb, hs] at h

/-- Helper: receiver comm case when candidate is a recv. -/
private theorem SoundRel_postfix_comm_receiver_recv
    (sender receiver role : String) (gbs : List (Label × GlobalType))
    (partner : String) (lbs : List BranchR) (hr : role = receiver)
    (hs : role ≠ sender)
    (h : SoundRel (.comm sender receiver gbs) role (.recv partner lbs)) :
    CProjectF SoundRel (.comm sender receiver gbs) role (.recv partner lbs) := by
  -- Reduce to the branch checker and convert it into a BranchesProjRel witness.
  have hsender : (role == sender) = false := beq_eq_false_iff_ne.mpr hs
  have hsender' : (receiver == sender) = false := by
    simpa [hr] using hsender
  have h' :
      (if (partner == sender) = true then projectbBranches gbs role lbs else false) = true := by
    simpa [SoundRel, projectb, hr, hsender'] using h
  by_cases hpartner : (partner == sender) = true
  · have hbranches : projectbBranches gbs role lbs = true := by
      simpa [hpartner] using h'
    have hbranches' : BranchesProjRel SoundRel gbs receiver lbs := by
      simpa [hr] using projectbBranches_to_SoundRel gbs role lbs hbranches
    have hpartner_eq : partner = sender := string_beq_eq_true_to_eq hpartner
    have hns : receiver ≠ sender := by
      simpa [hr] using hs
    simpa [CProjectF, hr, hns] using ⟨hpartner_eq, hbranches'⟩
  · have hfalse : False := by
      simp [hpartner] at h'
    exact hfalse.elim

/-- SoundRel postfix: comm case for receiver role. -/
private theorem SoundRel_postfix_comm_receiver
    (sender receiver role : String) (gbs : List (Label × GlobalType))
    (cand : LocalTypeR) (hr : role = receiver) (hs : role ≠ sender)
    (h : SoundRel (.comm sender receiver gbs) role cand) :
    CProjectF SoundRel (.comm sender receiver gbs) role cand := by
  -- Receiver projections must be receives with matching partner and projected branches.
  cases cand with
  | recv partner lbs =>
      -- Delegate to the specialized recv-case helper.
      exact SoundRel_postfix_comm_receiver_recv sender receiver role gbs partner lbs hr hs h
  | «end» =>
      -- projectb reduces to false for non-recv candidates under receiver role.
      have hsender' : (receiver == sender) = false := by
        simpa [hr] using beq_eq_false_iff_ne.mpr hs
      simp [SoundRel, projectb, hr, hsender'] at h
  | var _ =>
      have hsender' : (receiver == sender) = false := by
        simpa [hr] using beq_eq_false_iff_ne.mpr hs
      simp [SoundRel, projectb, hr, hsender'] at h
  | send _ _ =>
      have hsender' : (receiver == sender) = false := by
        simpa [hr] using beq_eq_false_iff_ne.mpr hs
      simp [SoundRel, projectb, hr, hsender'] at h
  | mu _ _ =>
      have hsender' : (receiver == sender) = false := by
        simpa [hr] using beq_eq_false_iff_ne.mpr hs
      simp [SoundRel, projectb, hr, hsender'] at h

/-- SoundRel postfix: comm case for non-participant role. -/
private theorem SoundRel_postfix_comm_other
    (sender receiver role : String) (gbs : List (Label × GlobalType))
    (cand : LocalTypeR) (hs : role ≠ sender) (hr : role ≠ receiver)
    (h : SoundRel (.comm sender receiver gbs) role cand) :
    CProjectF SoundRel (.comm sender receiver gbs) role cand := by
  -- Non-participants must project all branches to the same candidate.
  have hsender : (role == sender) = false := beq_eq_false_iff_ne.mpr hs
  have hreceiver : (role == receiver) = false := beq_eq_false_iff_ne.mpr hr
  have h' := h
  dsimp [SoundRel] at h'
  unfold projectb at h'
  simp [hsender, hreceiver] at h'
  have hbranches := projectbAllBranches_to_SoundRel gbs role cand h'
  simpa [CProjectF, hs, hr] using hbranches

/-- Delegate case when role is delegator. -/
private theorem SoundRel_postfix_delegate_delegator
    (p q : String) (sid : Nat) (r : String) (cont : GlobalType)
    (role : String) (cand : LocalTypeR)
    (hp : role = p) (h : SoundRel (.delegate p q sid r cont) role cand) :
    CProjectF SoundRel (.delegate p q sid r cont) role cand := by
  have hpf : (role == p) = true := by
    simpa [hp] using (beq_self_eq_true (a := p))
  cases cand with
  | send partner lbs =>
      cases lbs with
      | nil =>
          have hfalse : False := by
            simpa [SoundRel, projectb, hp, hpf] using h
          exact hfalse.elim
      | cons b bs =>
          cases bs with
          | nil =>
              cases b with
              | mk lbl rest =>
                  cases rest with
                  | mk vt contCand =>
                      have h' :
                          (if partner == q then
                            if lbl == ⟨"_delegate", .unit⟩ then
                              if vt == some (.chan sid r) then projectb cont role contCand else false
                            else false
                          else false) = true := by
                        simpa [SoundRel, projectb, hpf] using h
                      by_cases hpartner : (partner == q) = true
                      · have h'' := h'; simp [hpartner] at h''
                        by_cases hlbl : (lbl == ⟨"_delegate", .unit⟩) = true
                        · have h''' := h''; simp [hlbl] at h'''
                          by_cases hvt : (vt == some (.chan sid r)) = true
                          · have hcont : projectb cont role contCand = true := by
                              simpa [hvt] using h'''
                            have hpartner_eq : partner = q := string_beq_eq_true_to_eq hpartner
                            have hlbl_eq : lbl = ⟨"_delegate", .unit⟩ :=
                              label_beq_eq_true_to_eq hlbl
                            have hvt_eq : vt = some (.chan sid r) :=
                              optionValType_beq_eq_true_to_eq hvt
                            have hcont' : SoundRel cont role contCand := hcont
                            have hcont'' : SoundRel cont p contCand := by
                              simpa [hp] using hcont'
                            simp [CProjectF, hp, hpartner_eq, hlbl_eq, hvt_eq, hcont'']
                          · have hfalse : False := by simp [hvt] at h'''
                            exact hfalse.elim
                        · have hfalse : False := by simp [hlbl] at h''
                          exact hfalse.elim
                      · have hfalse : False := by simp [hpartner] at h'
                        exact hfalse.elim
          | cons b2 bs2 =>
              have hfalse : False := by
                dsimp [SoundRel] at h
                unfold projectb at h
                simpa [hp] using h
              exact hfalse.elim
  | recv _ _ =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hp] using h
      exact hfalse.elim
  | «end» =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hp] using h
      exact hfalse.elim
  | var _ =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hp] using h
      exact hfalse.elim
  | mu _ _ =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hp] using h
      exact hfalse.elim

/-- Delegate case when role is delegatee. -/
private theorem SoundRel_postfix_delegate_delegatee
    (p q : String) (sid : Nat) (r : String) (cont : GlobalType)
    (role : String) (cand : LocalTypeR)
    (hqeq : role = q) (hp : role ≠ p) (h : SoundRel (.delegate p q sid r cont) role cand) :
    CProjectF SoundRel (.delegate p q sid r cont) role cand := by
  have hqf : (role == q) = true := by
    simpa [hqeq] using (beq_self_eq_true (a := q))
  cases cand with
  | recv partner lbs =>
      cases lbs with
      | nil =>
          have hfalse : False := by
            simpa [SoundRel, projectb, hqeq, hqf, beq_false_of_ne hp] using h
          exact hfalse.elim
      | cons b bs =>
          cases bs with
          | nil =>
              cases b with
              | mk lbl rest =>
                  cases rest with
                  | mk vt contCand =>
                      have hpf : (role == p) = false := by simpa using beq_false_of_ne hp
                      have htmp :
                          ¬ q = p ∧
                            partner = p ∧
                              (lbl == ⟨"_delegate", .unit⟩) = true ∧
                                (vt == some (.chan sid r)) = true ∧
                                  projectb cont role contCand = true := by
                        simpa [SoundRel, projectb, hpf, hqeq] using h
                      have h' :
                          partner = p ∧
                            (lbl == ⟨"_delegate", .unit⟩) = true ∧
                              (vt == some (.chan sid r)) = true ∧
                                projectb cont role contCand = true := htmp.2
                      rcases h' with ⟨hpartner_eq, hlbl, hvt, hcont⟩
                      have hlbl_eq : lbl = ⟨"_delegate", .unit⟩ :=
                        label_beq_eq_true_to_eq hlbl
                      have hvt_eq : vt = some (.chan sid r) :=
                        optionValType_beq_eq_true_to_eq hvt
                      have hcont' : SoundRel cont role contCand := hcont
                      have hcont'' : SoundRel cont q contCand := by
                        simpa [hqeq] using hcont'
                      have hqp : q ≠ p := by
                        intro hqp
                        exact hp (by simpa [hqeq] using hqp)
                      subst hqeq
                      simp [CProjectF, hqp, hpartner_eq, hlbl_eq, hvt_eq, hcont'']
          | cons b2 bs2 =>
              have hfalse : False := by
                dsimp [SoundRel] at h
                unfold projectb at h
                simpa [hqeq, beq_false_of_ne hp] using h
              exact hfalse.elim
  | send _ _ =>
      have hqp : q ≠ p := by
        intro hqp
        exact hp (by simpa [hqeq] using hqp)
      dsimp [SoundRel] at h
      unfold projectb at h
      by_cases hqp' : q = p
      · exact (False.elim (hqp hqp'))
      · simp [hqeq, hqp'] at h
  | «end» =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hqeq, beq_false_of_ne hp] using h
      exact hfalse.elim
  | var _ =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hqeq, beq_false_of_ne hp] using h
      exact hfalse.elim
  | mu _ _ =>
      have hfalse : False := by
        dsimp [SoundRel] at h
        unfold projectb at h
        simpa [hqeq, beq_false_of_ne hp] using h
      exact hfalse.elim

/-- Delegate case when role is non-participant. -/
private theorem SoundRel_postfix_delegate_other
    (p q : String) (sid : Nat) (r : String) (cont : GlobalType)
    (role : String) (cand : LocalTypeR)
    (hp : role ≠ p) (hq : role ≠ q)
    (h : SoundRel (.delegate p q sid r cont) role cand) :
    CProjectF SoundRel (.delegate p q sid r cont) role cand := by
  dsimp [SoundRel] at h
  unfold projectb at h
  have hpf : (role == p) = false := by simpa using beq_false_of_ne hp
  have hqf : (role == q) = false := by simpa using beq_false_of_ne hq
  simp only [hpf, Bool.false_eq_true, ↓reduceIte, hqf] at h
  -- Goal is CProjectF SoundRel (.delegate p q sid r cont) role cand
  -- For non-participant (role ≠ p and role ≠ q): CProjectF gives SoundRel cont role cand
  unfold CProjectF
  have hpf' : role = p ↔ False := by simp [hp]
  have hqf' : role = q ↔ False := by simp [hq]
  simp only [hpf', ↓reduceIte, hqf']
  dsimp [SoundRel]
  exact h

/-- SoundRel is a post-fixpoint of CProjectF. -/
private theorem SoundRel_postfix :
    ∀ g role cand, SoundRel g role cand → CProjectF SoundRel g role cand := by
  intro g role cand h
  -- Dispatch on the global constructor and role case.
  cases g with
  | «end» => exact SoundRel_postfix_end role cand h
  | var t => exact SoundRel_postfix_var t role cand h
  | mu t body => exact SoundRel_postfix_mu t body role cand h
  | comm sender receiver gbs =>
      by_cases hs : role = sender
      · exact SoundRel_postfix_comm_sender sender receiver role gbs cand hs h
      · by_cases hr : role = receiver
        · exact SoundRel_postfix_comm_receiver sender receiver role gbs cand hr hs h
        · exact SoundRel_postfix_comm_other sender receiver role gbs cand hs hr h
  | delegate p q sid r cont =>
      by_cases hp : role = p
      · exact SoundRel_postfix_delegate_delegator p q sid r cont role cand hp h
      · by_cases hq : role = q
        · exact SoundRel_postfix_delegate_delegatee p q sid r cont role cand hq hp h
        · exact SoundRel_postfix_delegate_other p q sid r cont role cand hp hq h

/-- Soundness: if projectb returns true, then CProject holds. -/
theorem projectb_sound (g : GlobalType) (role : String) (cand : LocalTypeR)
    (h : projectb g role cand = true) : CProject g role cand := by
  -- Use the SoundRel post-fixpoint and coinduction.
  have hinR : SoundRel g role cand := h
  exact CProject_coind SoundRel_postfix g role cand hinR

/-- Helper: BranchesProjRel CProject implies projectbBranches.
    The ih provides recursive evidence that for each branch global type,
    if CProject holds then projectb returns true. -/
theorem BranchesProjRel_to_projectbBranches
    (gbs : List (Label × GlobalType)) (role : String) (lbs : List BranchR)
    (hrel : BranchesProjRel CProject gbs role lbs)
    (ih : ∀ gb ∈ gbs, ∀ lb, CProject gb.2 role lb → projectb gb.2 role lb = true) :
    projectbBranches gbs role lbs = true := by
  induction hrel with
  | nil => simp only [projectbBranches]
  | @cons ghd lhd gtl ltl hpair hrest ihrest =>
      obtain ⟨hlabel, hnone, hproj⟩ := hpair
      unfold projectbBranches
      -- hlabel : ghd.1 = lhd.1, so we need (ghd.1 == lhd.1) = true
      have hbeq : (ghd.1 == lhd.1) = true := eq_to_label_beq_eq_true hlabel
      have hvt : (lhd.2.1 == none) = true := by
        cases lhd with
        | mk lbl rest =>
            cases rest with
            | mk vt cont =>
                cases vt with
                | none => rfl
                | some t =>
                    cases hnone
      simp only [hbeq, hvt, ↓reduceIte, Bool.and_eq_true]
      constructor
      · exact ih ghd (List.Mem.head gtl) lhd.2.2 hproj
      · exact ihrest (fun gb hmem lb hcp => ih gb (List.Mem.tail ghd hmem) lb hcp)

/-- Helper: AllBranchesProj CProject implies projectbAllBranches.
    The ih provides recursive evidence that for each branch global type,
    if CProject holds then projectb returns true. -/
theorem AllBranchesProj_to_projectbAllBranches
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

end Choreography.Projection.Projectb
