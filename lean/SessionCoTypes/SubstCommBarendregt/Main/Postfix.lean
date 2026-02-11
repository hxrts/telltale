import SessionCoTypes.SubstCommBarendregt.Main.StandardCase

/-! # SessionCoTypes.SubstCommBarendregt.Main.Postfix

Standard constructor case analysis for `SubstRel_postfix_standard`.
-/

/-
The Problem. Prove `SubstRel` is closed under one-step EQ2 unfolding.
Solution Structure. Constructor-by-constructor EQ2F case analysis.
-/

namespace SessionCoTypes.SubstCommBarendregt
open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2
open SessionTypes.GlobalType

/-! ## Standard Case Analysis -/

theorem SubstRel_postfix_standard (var : String) (repl : LocalTypeR)
    (a b : LocalTypeR) (_hab : EQ2 a b)
    (hbarA : notBoundAt var a = true) (hbarB : notBoundAt var b = true)
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hf : EQ2F EQ2 a b) :
    EQ2F (EQ2_closure (SubstRel var repl)) (a.substitute var repl) (b.substitute var repl) := by
  cases a <;> cases b
  -- end-end
  case end.end =>
    unfold LocalTypeR.substitute
    unfold EQ2F
    trivial
  -- var-var
  case var.var x y =>
    unfold LocalTypeR.substitute
    unfold EQ2F at hf ⊢
    by_cases hx : x == var
    · -- x == var
      simp only [hx, ite_true]
      by_cases hy : y == var
      · -- y == var, both become repl
        simp only [hy, ite_true]
        -- Goal: EQ2F (EQ2_closure (SubstRel var repl)) repl repl
        have hf' : EQ2F EQ2 repl repl := EQ2.destruct (EQ2_refl repl)
        exact EQ2F.mono (fun _ _ h => Or.inr h) repl repl hf'
      · -- y != var, x == var but hf says x = y
        simp only [hy, Bool.false_eq_true, ite_false]
        simp only [beq_iff_eq] at hx hy hf
        exact absurd (hf.symm.trans hx) hy
    · -- x != var
      simp only [hx, Bool.false_eq_true, ite_false]
      by_cases hy : y == var
      · simp only [hy, ite_true]
        simp only [beq_iff_eq] at hx hy hf
        exact absurd (hf.trans hy) hx
      · simp only [hy, Bool.false_eq_true, ite_false]
        exact hf
  -- send-send
  case send.send p bs q cs =>
    unfold LocalTypeR.substitute
    unfold EQ2F at hf ⊢
    unfold notBoundAt at hbarA hbarB
    obtain ⟨hp, hbranches⟩ := hf
    exact ⟨hp, BranchesRel_substitute var repl bs cs hbranches hbarA hbarB hfresh⟩
  -- recv-recv
  case recv.recv p bs q cs =>
    unfold LocalTypeR.substitute
    unfold EQ2F at hf ⊢
    unfold notBoundAt at hbarA hbarB
    obtain ⟨hp, hbranches⟩ := hf
    exact ⟨hp, BranchesRel_substitute var repl bs cs hbranches hbarA hbarB hfresh⟩
  -- mu-mu
  case mu.mu t body s body' =>
    unfold notBoundAt at hbarA hbarB
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have htne : t ≠ var := Ne.symm (bne_iff_ne.mp hvart)
    have hsne : s ≠ var := Ne.symm (bne_iff_ne.mp hvars)
    have htvar : (t == var) = false := beq_eq_false_iff_ne.mpr htne
    have hsvar : (s == var) = false := beq_eq_false_iff_ne.mpr hsne
    -- notBoundAt for the mu constructors
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    -- Explicit substitution reductions
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    simp only [ha_subst, hb_subst, EQ2F] at hf ⊢
    obtain ⟨hleft, hright⟩ := hf
    constructor
    · -- Left goal: SubstRel ((body.subst t (mu t body)).subst var repl) ((mu s body').subst var repl)
      rw [subst_mu_comm body var t repl hbarBody hfresh htne]
      apply Or.inl
      rw [← hb_subst]
      exact SubstRel.base _ _ hleft
        (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
        hmu_s_bar
    · -- Right goal: SubstRel ((mu t body).subst var repl) ((body'.subst s (mu s body')).subst var repl)
      rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
      apply Or.inl
      rw [← ha_subst]
      exact SubstRel.base _ _ hright
        hmu_t_bar
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
  -- mu-end (unfolding on left)
  case mu.end t body =>
    have htvar := bne_of_notBoundAt_mu hbarA
    unfold notBoundAt at hbarA
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst : LocalTypeR.end.substitute var repl = .end := rfl
    simp only [ha_subst, hb_subst, EQ2F] at hf ⊢
    rw [subst_mu_comm body var t repl hbarBody hfresh htne]
    apply Or.inl
    exact SubstRel.base _ _ hf
      (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
      (by rfl)
  case mu.var t body v =>
    have htvar := bne_of_notBoundAt_mu hbarA
    unfold notBoundAt at hbarA
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    -- hf : EQ2F EQ2 (.mu t body) (.var v) = EQ2 (body.substitute t (.mu t body)) (.var v)
    simp only [EQ2F_mu_var] at hf
    -- Goal: EQ2F (EQ2_closure (SubstRel var repl)) ((.mu t body).substitute var repl) ((.var v).substitute var repl)
    -- Don't simp goal - instead use SubstRel.base directly with unfold_left
    -- SubstRel.base constructs: SubstRel var repl (a.subst var repl) (b.subst var repl)
    -- We need: EQ2F (EQ2_closure ...) ((.mu t body).subst var repl) ((.var v).subst var repl)
    -- By EQ2F_mu_var: this = EQ2_closure ... (((.mu t body).subst var repl).unfold) ((.var v).subst var repl)
    -- (.mu t body).subst var repl = .mu t (body.subst var repl) (since t ≠ var)
    -- unfold of that = (body.subst var repl).subst t (.mu t (body.subst var repl))
    have ha_subst := mu_substitute_ne t body var repl htvar
    -- Use EQ2F reduction on the substituted forms
    rw [ha_subst]
    -- Now goal: EQ2F (EQ2_closure ...) (.mu t (body.subst var repl)) ((.var v).subst var repl)
    by_cases hv : v == var
    · have hb_subst := var_substitute_eq v var repl hv
      rw [hb_subst]
      -- Goal: EQ2F (EQ2_closure ...) (.mu t (body.subst var repl)) repl
      -- repl is arbitrary, so we need to case-split on its constructor
      cases repl with
      | «end» =>
        simp only [EQ2F_mu_end]
        rw [subst_mu_comm body var t (.end) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var .end ((body.substitute t (.mu t body)).substitute var .end)
            ((LocalTypeR.var v).substitute var .end) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var .end hv] at hsr
        exact hsr
      | var w =>
        simp only [EQ2F_mu_var]
        rw [subst_mu_comm body var t (.var w) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var (.var w) ((body.substitute t (.mu t body)).substitute var (.var w))
            ((LocalTypeR.var v).substitute var (.var w)) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var (.var w) hv] at hsr
        exact hsr
      | send p bs =>
        simp only [EQ2F_mu_send]
        rw [subst_mu_comm body var t (.send p bs) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var (.send p bs) ((body.substitute t (.mu t body)).substitute var (.send p bs))
            ((LocalTypeR.var v).substitute var (.send p bs)) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var (.send p bs) hv] at hsr
        exact hsr
      | recv p bs =>
        simp only [EQ2F_mu_recv]
        rw [subst_mu_comm body var t (.recv p bs) hbarBody (by intro t'; exact hfresh t') htne]
        apply Or.inl
        have hsr : SubstRel var (.recv p bs) ((body.substitute t (.mu t body)).substitute var (.recv p bs))
            ((LocalTypeR.var v).substitute var (.recv p bs)) :=
          SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
            (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
            (by rfl : notBoundAt var (.var v) = true)
        rw [var_substitute_eq v var (.recv p bs) hv] at hsr
        exact hsr
      | mu s body' =>
        -- mu-mu case is more complex - need both directions
        simp only [EQ2F]
        constructor
        · -- left goal: (body.subst var (.mu s body')).subst t (...) relates to (.mu s body')
          rw [subst_mu_comm body var t (.mu s body') hbarBody (by intro t'; exact hfresh t') htne]
          apply Or.inl
          have hsr : SubstRel var (.mu s body') ((body.substitute t (.mu t body)).substitute var (.mu s body'))
              ((LocalTypeR.var v).substitute var (.mu s body')) :=
            SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
              (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
              (by rfl : notBoundAt var (.var v) = true)
          rw [var_substitute_eq v var (.mu s body') hv] at hsr
          exact hsr
        · -- right goal: (.mu t (body.subst var (.mu s body'))) relates to (body'.subst s (.mu s body'))
          -- SubstRel.base gives us: SubstRel (.mu t (body.subst var repl)) repl
          -- We need to unfold the RHS: repl.unfold = body'.subst s (.mu s body')
          apply Or.inl
          have hab : EQ2 (.mu t body) (.var v) := by
            apply EQ2.construct
            simp only [EQ2F_mu_var]
            exact hf
          have hsr_base : SubstRel var (LocalTypeR.mu s body')
              ((LocalTypeR.mu t body).substitute var (LocalTypeR.mu s body'))
              ((LocalTypeR.var v).substitute var (LocalTypeR.mu s body')) :=
            SubstRel.base (LocalTypeR.mu t body) (LocalTypeR.var v) hab hmu_t_bar (by rfl : notBoundAt var (LocalTypeR.var v) = true)
          -- Reduce substitutions in hsr_base's type
          have hmu_subst : (LocalTypeR.mu t body).substitute var (LocalTypeR.mu s body')
              = LocalTypeR.mu t (body.substitute var (LocalTypeR.mu s body')) :=
            mu_substitute_ne t body var (LocalTypeR.mu s body') htvar
          have hvar_subst : (LocalTypeR.var v).substitute var (LocalTypeR.mu s body')
              = LocalTypeR.mu s body' :=
            var_substitute_eq v var (LocalTypeR.mu s body') hv
          -- The types are definitionally equal after reducing substitute
          -- Use cast with Eq.mpr to convert between them
          have hsr : SubstRel var (LocalTypeR.mu s body')
              (LocalTypeR.mu t (body.substitute var (LocalTypeR.mu s body')))
              (LocalTypeR.mu s body') := by
            have heq : SubstRel var (LocalTypeR.mu s body')
                ((LocalTypeR.mu t body).substitute var (LocalTypeR.mu s body'))
                ((LocalTypeR.var v).substitute var (LocalTypeR.mu s body'))
              = SubstRel var (LocalTypeR.mu s body')
                (LocalTypeR.mu t (body.substitute var (LocalTypeR.mu s body')))
                (LocalTypeR.mu s body') := by
              rw [hmu_subst, hvar_subst]
            exact heq ▸ hsr_base
          -- Apply unfold_right: (.mu s body').unfold = body'.substitute s (.mu s body')
          have hsr' := SubstRel.unfold_right hsr
          -- Reduce the unfold in the type
          simp only [LocalTypeR.unfold] at hsr'
          exact hsr'
    · have hv' : (v == var) = false := by cases h : v == var <;> simp_all
      have hb_subst := var_substitute_ne v var repl hv'
      rw [hb_subst]
      -- Goal: EQ2F (EQ2_closure ...) (.mu t (body.subst var repl)) (.var v)
      simp only [EQ2F_mu_var]
      rw [subst_mu_comm body var t repl hbarBody hfresh htne]
      apply Or.inl
      have hsr : SubstRel var repl ((body.substitute t (.mu t body)).substitute var repl)
          ((LocalTypeR.var v).substitute var repl) :=
        SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.var v) hf
          (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
          (by rfl : notBoundAt var (.var v) = true)
      rw [hb_subst] at hsr
      exact hsr
  case mu.send t body p bs =>
    have htvar := bne_of_notBoundAt_mu hbarA
    have hbarB_orig := hbarB  -- Save before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst : (LocalTypeR.send p bs).substitute var repl = .send p (SessionTypes.LocalTypeR.substituteBranches bs var repl) := rfl
    -- Use EQ2F reduction lemma
    simp only [EQ2F_mu_send] at hf
    simp only [ha_subst, hb_subst, EQ2F_mu_send]
    rw [subst_mu_comm body var t repl hbarBody hfresh htne]
    apply Or.inl
    have hsr : SubstRel var repl ((body.substitute t (.mu t body)).substitute var repl)
        ((LocalTypeR.send p bs).substitute var repl) :=
      SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.send p bs) hf
        (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
        hbarB_orig
    rw [hb_subst] at hsr
    exact hsr
  case mu.recv t body p bs =>
    have htvar := bne_of_notBoundAt_mu hbarA
    have hbarB_orig := hbarB  -- Save before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvart, hbarBody⟩ := Bool.and_eq_true_iff.mp hbarA
    have htne : t ≠ var := by simp only [bne_iff_ne, ne_eq] at hvart; exact fun h => hvart h.symm
    have hmu_t_bar : notBoundAt var (.mu t body) = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvart, hbarBody⟩
    have ha_subst := mu_substitute_ne t body var repl htvar
    have hb_subst : (LocalTypeR.recv p bs).substitute var repl = .recv p (SessionTypes.LocalTypeR.substituteBranches bs var repl) := rfl
    -- Use EQ2F reduction lemma
    simp only [EQ2F_mu_recv] at hf
    simp only [ha_subst, hb_subst, EQ2F_mu_recv]
    rw [subst_mu_comm body var t repl hbarBody hfresh htne]
    apply Or.inl
    have hsr : SubstRel var repl ((body.substitute t (.mu t body)).substitute var repl)
        ((LocalTypeR.recv p bs).substitute var repl) :=
      SubstRel.base (body.substitute t (.mu t body)) (LocalTypeR.recv p bs) hf
        (notBoundAt_subst var t body (.mu t body) hbarBody hmu_t_bar)
        hbarB_orig
    rw [hb_subst] at hsr
    exact hsr
  -- end-mu (unfolding on right)
  case end.mu s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    unfold notBoundAt at hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have ha_subst : LocalTypeR.end.substitute var repl = .end := rfl
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_end_mu] at hf
    simp only [ha_subst, hb_subst, EQ2F_end_mu]
    rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
    apply Or.inl
    have hsr : SubstRel var repl (LocalTypeR.end.substitute var repl)
        ((body'.substitute s (.mu s body')).substitute var repl) :=
      SubstRel.base LocalTypeR.end (body'.substitute s (.mu s body')) hf
        (by rfl : notBoundAt var LocalTypeR.end = true)
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
    rw [ha_subst] at hsr
    exact hsr
  case var.mu v s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    unfold notBoundAt at hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_var_mu] at hf
    by_cases hv : v == var
    · -- v == var: LHS substitutes to repl
      have ha_subst := var_substitute_eq v var repl hv
      -- repl is arbitrary, so we need to case-split on its constructor
      cases repl with
      | «end» =>
        simp only [ha_subst, hb_subst, EQ2F_end_mu]
        rw [subst_mu_comm body' var s (.end) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var .end ((LocalTypeR.var v).substitute var .end)
            ((body'.substitute s (.mu s body')).substitute var .end) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var .end hv] at hsr
        exact hsr
      | var w =>
        simp only [ha_subst, hb_subst, EQ2F_var_mu]
        rw [subst_mu_comm body' var s (.var w) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var (.var w) ((LocalTypeR.var v).substitute var (.var w))
            ((body'.substitute s (.mu s body')).substitute var (.var w)) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var (.var w) hv] at hsr
        exact hsr
      | send p bs =>
        simp only [ha_subst, hb_subst, EQ2F_send_mu]
        rw [subst_mu_comm body' var s (.send p bs) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var (.send p bs) ((LocalTypeR.var v).substitute var (.send p bs))
            ((body'.substitute s (.mu s body')).substitute var (.send p bs)) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var (.send p bs) hv] at hsr
        exact hsr
      | recv p bs =>
        simp only [ha_subst, hb_subst, EQ2F_recv_mu]
        rw [subst_mu_comm body' var s (.recv p bs) hbarBody' (by intro t'; exact hfresh t') hsne]
        apply Or.inl
        have hsr : SubstRel var (.recv p bs) ((LocalTypeR.var v).substitute var (.recv p bs))
            ((body'.substitute s (.mu s body')).substitute var (.recv p bs)) :=
          SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
            (by rfl : notBoundAt var (LocalTypeR.var v) = true)
            (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
        rw [var_substitute_eq v var (.recv p bs) hv] at hsr
        exact hsr
      | mu t body =>
        -- mu-mu case: need both directions
        simp only [ha_subst, hb_subst, EQ2F]
        constructor
        · -- left goal: (body.subst t (.mu t body)) relates to (.mu s (body'.subst var (.mu t body)))
          -- SubstRel.base gives us: SubstRel (.mu t body) (.mu s (body'.subst var repl))
          -- We need to unfold the LHS: (.mu t body).unfold = body.subst t (.mu t body)
          apply Or.inl
          have hab : EQ2 (.var v) (.mu s body') := by
            apply EQ2.construct
            simp only [EQ2F_var_mu]
            exact hf
          have hsr_base : SubstRel var (LocalTypeR.mu t body)
              ((LocalTypeR.var v).substitute var (LocalTypeR.mu t body))
              ((LocalTypeR.mu s body').substitute var (LocalTypeR.mu t body)) :=
            SubstRel.base (LocalTypeR.var v) (LocalTypeR.mu s body') hab (by rfl : notBoundAt var (LocalTypeR.var v) = true) hmu_s_bar
          -- Reduce substitutions in hsr_base's type
          have hvar_subst : (LocalTypeR.var v).substitute var (LocalTypeR.mu t body)
              = LocalTypeR.mu t body :=
            var_substitute_eq v var (LocalTypeR.mu t body) hv
          have hmu_subst : (LocalTypeR.mu s body').substitute var (LocalTypeR.mu t body)
              = LocalTypeR.mu s (body'.substitute var (LocalTypeR.mu t body)) :=
            mu_substitute_ne s body' var (LocalTypeR.mu t body) hsvar
          -- The types are definitionally equal after reducing substitute
          -- Use cast with Eq.mpr to convert between them
          have hsr : SubstRel var (LocalTypeR.mu t body)
              (LocalTypeR.mu t body)
              (LocalTypeR.mu s (body'.substitute var (LocalTypeR.mu t body))) := by
            have heq : SubstRel var (LocalTypeR.mu t body)
                ((LocalTypeR.var v).substitute var (LocalTypeR.mu t body))
                ((LocalTypeR.mu s body').substitute var (LocalTypeR.mu t body))
              = SubstRel var (LocalTypeR.mu t body)
                (LocalTypeR.mu t body)
                (LocalTypeR.mu s (body'.substitute var (LocalTypeR.mu t body))) := by
              rw [hvar_subst, hmu_subst]
            exact heq ▸ hsr_base
          -- Apply unfold_left: (.mu t body).unfold = body.substitute t (.mu t body)
          have hsr' := SubstRel.unfold_left hsr
          -- Reduce the unfold in the type
          simp only [LocalTypeR.unfold] at hsr'
          exact hsr'
        · -- right goal: (.mu t body) relates to (body'.subst s (.mu s body')).subst var (.mu t body)
          rw [subst_mu_comm body' var s (.mu t body) hbarBody' (by intro t'; exact hfresh t') hsne]
          apply Or.inl
          have hsr : SubstRel var (.mu t body) ((LocalTypeR.var v).substitute var (.mu t body))
              ((body'.substitute s (.mu s body')).substitute var (.mu t body)) :=
            SubstRel.base (LocalTypeR.var v) (body'.substitute s (.mu s body')) hf
              (by rfl : notBoundAt var (LocalTypeR.var v) = true)
              (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
          rw [var_substitute_eq v var (.mu t body) hv] at hsr
          exact hsr
    · -- v != var: LHS stays as .var v
      have hv' : (v == var) = false := by cases h : v == var <;> simp_all
      have ha_subst := var_substitute_ne v var repl hv'
      simp only [ha_subst, hb_subst, EQ2F_var_mu]
      rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
      apply Or.inl
      have hsr : SubstRel var repl ((LocalTypeR.var v).substitute var repl)
          ((body'.substitute s (LocalTypeR.mu s body')).substitute var repl) :=
        SubstRel.base (LocalTypeR.var v) (body'.substitute s (LocalTypeR.mu s body')) hf
          (by rfl : notBoundAt var (LocalTypeR.var v) = true)
          (notBoundAt_subst var s body' (LocalTypeR.mu s body') hbarBody' hmu_s_bar)
      rw [ha_subst] at hsr
      exact hsr
  case send.mu p bs s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    have hbarA_orig := hbarA  -- Save original before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have ha_subst : (LocalTypeR.send p bs).substitute var repl = .send p (SessionTypes.LocalTypeR.substituteBranches bs var repl) := rfl
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_send_mu] at hf
    simp only [ha_subst, hb_subst, EQ2F_send_mu]
    rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
    apply Or.inl
    have hsr : SubstRel var repl ((LocalTypeR.send p bs).substitute var repl)
        ((body'.substitute s (.mu s body')).substitute var repl) :=
      SubstRel.base (LocalTypeR.send p bs) (body'.substitute s (.mu s body')) hf
        hbarA_orig
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
    rw [ha_subst] at hsr
    exact hsr
  case recv.mu p bs s body' =>
    have hsvar := bne_of_notBoundAt_mu hbarB
    have hbarA_orig := hbarA  -- Save original before unfolding
    unfold notBoundAt at hbarA hbarB
    have ⟨hvars, hbarBody'⟩ := Bool.and_eq_true_iff.mp hbarB
    have hsne : s ≠ var := by simp only [bne_iff_ne, ne_eq] at hvars; exact fun h => hvars h.symm
    have hmu_s_bar : notBoundAt var (.mu s body') = true := by
      unfold notBoundAt; exact Bool.and_eq_true_iff.mpr ⟨hvars, hbarBody'⟩
    have ha_subst : (LocalTypeR.recv p bs).substitute var repl = .recv p (SessionTypes.LocalTypeR.substituteBranches bs var repl) := rfl
    have hb_subst := mu_substitute_ne s body' var repl hsvar
    -- Use EQ2F reduction lemma
    simp only [EQ2F_recv_mu] at hf
    simp only [ha_subst, hb_subst, EQ2F_recv_mu]
    rw [subst_mu_comm body' var s repl hbarBody' hfresh hsne]
    apply Or.inl
    have hsr : SubstRel var repl ((LocalTypeR.recv p bs).substitute var repl)
        ((body'.substitute s (.mu s body')).substitute var repl) :=
      SubstRel.base (LocalTypeR.recv p bs) (body'.substitute s (.mu s body')) hf
        hbarA_orig
        (notBoundAt_subst var s body' (.mu s body') hbarBody' hmu_s_bar)
    rw [ha_subst] at hsr
    exact hsr
  -- Impossible cases (structurally incompatible constructors)
  case end.var | end.send | end.recv =>
    unfold EQ2F at hf; exact hf.elim
  case var.end | var.send | var.recv =>
    unfold EQ2F at hf; exact hf.elim
  case send.end | send.var | send.recv =>
    unfold EQ2F at hf; exact hf.elim
  case recv.end | recv.var | recv.send =>
    unfold EQ2F at hf; exact hf.elim
end SessionCoTypes.SubstCommBarendregt
