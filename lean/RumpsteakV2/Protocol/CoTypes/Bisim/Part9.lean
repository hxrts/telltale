import RumpsteakV2.Protocol.CoTypes.Bisim.Part8

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

namespace RumpsteakV2.Protocol.CoTypes.Bisim
/-! ## RelImage lift for Bisim branches (closed/fixed-point case) -/

private theorem BranchesRelBisim_of_Bisim_with_relImage
    {f : LocalTypeR → LocalTypeR} {R : Rel}
    (h_rel : ∀ a b, Bisim a b → R a b)
    {bs cs : List (Label × LocalTypeR)}
    (hbr : BranchesRelBisim Bisim bs cs)
    (hfix_bs : ∀ lb ∈ bs, f lb.2 = lb.2)
    (hfix_cs : ∀ lc ∈ cs, f lc.2 = lc.2) :
    BranchesRelBisim (RelImage f R) bs cs := by
  unfold BranchesRelBisim at hbr ⊢
  induction hbr with
  | nil => exact List.Forall₂.nil
  | cons hbc hrest ih =>
      -- hbc : b.1 = c.1 ∧ Bisim b.2 c.2
      rename_i b c bs' cs'
      have hb_fix : f b.2 = b.2 := by
        simpa using hfix_bs b (List.Mem.head _)
      have hc_fix : f c.2 = c.2 := by
        simpa using hfix_cs c (List.Mem.head _)
      refine List.Forall₂.cons ?head ?tail
      · refine ⟨hbc.1, ?_⟩
        refine ⟨_, _, h_rel _ _ hbc.2, ?_, ?_⟩
        · exact hb_fix.symm
        · exact hc_fix.symm
      · exact ih (fun lb hm => hfix_bs _ (List.Mem.tail _ hm))
                 (fun lc hm => hfix_cs _ (List.Mem.tail _ hm))

private theorem WellFormed_substitute {a repl : LocalTypeR} (var : String)
    (hWFa : LocalTypeR.WellFormed a) (hWFrepl : LocalTypeR.WellFormed repl) :
    LocalTypeR.WellFormed (a.substitute var repl) := by
  have hclosed_env : ClosedUnder ((var, repl) :: ([] : Env)) a := by
    intro v hv
    have hnil : a.freeVars = [] := by
      have : a.freeVars.isEmpty = true := by
        simpa [LocalTypeR.isClosed] using hWFa.closed
      exact (List.isEmpty_eq_true _).1 this
    have : False := by simpa [hnil] using hv
    exact this.elim
  have hclosed_subst : ClosedUnder ([] : Env) (a.substitute var repl) :=
    closedUnder_substitute_closed (env := []) (t := a) var repl hWFrepl.closed hclosed_env
  have hclosed : (a.substitute var repl).isClosed :=
    (closedUnder_nil_iff_isClosed _).1 hclosed_subst
  have hcontr : (a.substitute var repl).isContractive = true :=
    LocalTypeR.isContractive_substitute a var repl hWFa.contractive hWFrepl.contractive hWFrepl.closed
  exact ⟨hclosed, hcontr⟩

private theorem WellFormed_mu_substitute {body repl : LocalTypeR} (x var : String)
    (hWFmu : LocalTypeR.WellFormed (.mu x body)) (hWFrepl : LocalTypeR.WellFormed repl) :
    LocalTypeR.WellFormed (.mu x (body.substitute var repl)) := by
  -- Extract properties from hWFmu
  have hmu_closed : (.mu x body : LocalTypeR).isClosed := hWFmu.closed
  have hmu_contr : (.mu x body : LocalTypeR).isContractive = true := hWFmu.contractive
  -- Break down isContractive for mu
  simp only [LocalTypeR.isContractive, Bool.and_eq_true] at hmu_contr
  obtain ⟨hguarded, hbody_contr⟩ := hmu_contr
  -- Prove closedness of the result
  have hclosed_result : (.mu x (body.substitute var repl) : LocalTypeR).isClosed := by
    simp only [LocalTypeR.isClosed, LocalTypeR.freeVars]
    have hbody_fvs : (body.freeVars.filter (· != x)).isEmpty = true := by
      simpa [LocalTypeR.isClosed, LocalTypeR.freeVars] using hmu_closed
    have hrepl_closed : repl.isClosed := hWFrepl.closed
    -- Substitution with closed repl preserves closedness modulo binder
    simp only [List.isEmpty_eq_true, List.filter_eq_nil_iff] at hbody_fvs ⊢
    intro v hv
    have hv' := LocalTypeR.freeVars_substitute_subset body var repl v hv
    cases hv' with
    | inl hrepl =>
        have hrepl_fvs_nil : repl.freeVars = [] := by
          have : repl.freeVars.isEmpty = true := by
            simpa [LocalTypeR.isClosed] using hrepl_closed
          exact (List.isEmpty_eq_true _).1 this
        simp only [hrepl_fvs_nil, List.not_mem_nil] at hrepl
    | inr hbody =>
        have hvne : v ≠ var := hbody.2
        have hv_in : v ∈ body.freeVars := hbody.1
        have hv_ne_x : ¬(v != x) = true := hbody_fvs v hv_in
        simp only [bne_iff_ne, ne_eq, not_not] at hv_ne_x
        subst hv_ne_x
        simp only [bne_self_eq_false]
        decide
  -- Prove contractiveness of the result
  have hcontr_result : (.mu x (body.substitute var repl) : LocalTypeR).isContractive = true := by
    simp only [LocalTypeR.isContractive, Bool.and_eq_true]
    constructor
    · exact LocalTypeR.isGuarded_substitute body var x repl hguarded hWFrepl.closed
    · exact LocalTypeR.isContractive_substitute body var repl hbody_contr hWFrepl.contractive hWFrepl.closed
  exact ⟨hclosed_result, hcontr_result⟩

/-- When `UnfoldsToVar x var`, substituting `var → repl` yields something EQ2-equivalent to `repl`.

    Proof sketch: By induction on `UnfoldsToVar x var`:
    - Base case: x = .var var, so x.substitute var repl = repl, and EQ2_refl applies.
    - Mu case: x = .mu t body where body.substitute t (.mu t body) unfolds to var.
      The mu case with t = var is impossible (would require infinite proof).
      For t ≠ var, use EQ2_subst_mu_comm and the IH, then compose via EQ2_trans_via_Bisim.

    Key insight: if t = var, then body.substitute var (.mu var body) would need to unfold
    to .var var, but each .var var gets replaced by .mu var body, creating infinite recursion.
    So t ≠ var in all mu cases. -/
theorem UnfoldsToVar_substitute_EQ2 {x : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : UnfoldsToVar x var) (hWFx : LocalTypeR.WellFormed x)
    (hWFrepl : LocalTypeR.WellFormed repl) : EQ2 (x.substitute var repl) repl := by
  refine (UnfoldsToVar.rec
    (motive := fun x var _ => LocalTypeR.WellFormed x → EQ2 (x.substitute var repl) repl)
    ?base ?mu h) hWFx
  · intro var _hWF
    -- x = .var var, so x.substitute var repl = repl
    simp only [LocalTypeR.substitute, beq_self_eq_true, ↓reduceIte]
    exact EQ2_refl _
  · intro t body var hinner ih hWFx
    -- x = .mu t body, body.substitute t (.mu t body) unfolds to var
    by_cases htv : t = var
    · -- Case t = var: IMPOSSIBLE
      have hnotfree := RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.isFreeIn_subst_mu_self body t
      have hinner' : UnfoldsToVar (body.substitute t (.mu t body)) t := htv ▸ hinner
      exact (False.elim (not_UnfoldsToVar_of_not_isFreeIn hnotfree hinner'))
    · -- Case t ≠ var: use EQ2_subst_mu_comm + IH (WF-gated trans)
      have htv_beq : (t == var) = false := beq_eq_false_iff_ne.mpr htv
      simp only [LocalTypeR.substitute, htv_beq, Bool.false_eq_true, ↓reduceIte]
      have hcomm := EQ2_subst_mu_comm body var t repl htv hWFx
      have hWF_unfold : LocalTypeR.WellFormed (body.substitute t (.mu t body)) :=
        LocalTypeR.WellFormed.unfold (t := .mu t body) hWFx
      have ih' : EQ2 ((body.substitute t (.mu t body)).substitute var repl) repl := ih hWF_unfold
      -- Well-formedness for the intermediate types
      have hWF_subst : LocalTypeR.WellFormed ((.mu t body : LocalTypeR).substitute var repl) :=
        WellFormed_substitute (var := var) hWFx hWFrepl
      have hWF_subst' : LocalTypeR.WellFormed (.mu t (body.substitute var repl)) := by
        simpa [LocalTypeR.substitute, htv_beq] using hWF_subst
      have hWF_left : LocalTypeR.WellFormed
          ((body.substitute var repl).substitute t (.mu t (body.substitute var repl))) := by
        simpa [LocalTypeR.unfold] using
          (LocalTypeR.WellFormed.unfold (t := (.mu t (body.substitute var repl))) hWF_subst')
      have hWF_right : LocalTypeR.WellFormed
          ((body.substitute t (.mu t body)).substitute var repl) :=
        WellFormed_substitute (var := var) hWF_unfold hWFrepl
      have hunfolded : EQ2 ((body.substitute var repl).substitute t (.mu t (body.substitute var repl))) repl :=
        EQ2_trans_via_Bisim hcomm ih' hWF_left hWF_right hWFrepl
      apply EQ2.construct
      cases repl with
      | «end» =>
        simp only [EQ2F]
        exact hunfolded
      | var v =>
        simp only [EQ2F]
        exact hunfolded
      | send p bs =>
        simp only [EQ2F]
        exact hunfolded
      | recv p bs =>
        simp only [EQ2F]
        exact hunfolded
      | mu s body' =>
        simp only [EQ2F]
        constructor
        · exact hunfolded
        · have hunfolded_right :
            EQ2 ((body.substitute var (.mu s body')).substitute t
                (.mu t (body.substitute var (.mu s body'))))
              (body'.substitute s (.mu s body')) :=
            EQ2_unfold_right hunfolded
          have hrefl : EQ2 (.mu t (body.substitute var (.mu s body')))
              (.mu t (body.substitute var (.mu s body'))) := EQ2_refl _
          have hrefl_destruct :
              EQ2F EQ2 (.mu t (body.substitute var (.mu s body')))
                (.mu t (body.substitute var (.mu s body'))) := EQ2.destruct hrefl
          have hmu_to_unfold :
              EQ2 (.mu t (body.substitute var (.mu s body')))
                ((body.substitute var (.mu s body')).substitute t
                  (.mu t (body.substitute var (.mu s body')))) := by
            simpa [EQ2F] using hrefl_destruct.2
          have hWF_repl_unfold :
              LocalTypeR.WellFormed (body'.substitute s (.mu s body')) :=
            LocalTypeR.WellFormed.unfold (t := .mu s body') hWFrepl
          exact EQ2_trans_via_Bisim hmu_to_unfold hunfolded_right hWF_subst' hWF_left hWF_repl_unfold

/-- When both types unfold to the substituted variable, their substitutions are BisimF-related.

    This is the key lemma for the eq_var case of substitute_compatible.

    Semantic soundness: If both x and y unfold to `.var var`, then after substituting
    `var → repl`, both become something that has the same observable behavior as `repl`.
    Since they both "go through" repl, they are Bisim-equivalent.

    Proof: By induction on UnfoldsToVar proofs. When x = y = .var var, both substitute
    to repl, and they're BisimF-related through any observable behavior that repl has.
    For mu cases, the substitution produces a mu whose unfolding relates back to repl. -/
theorem substitute_at_var_bisimF {x y : LocalTypeR} {var : String} {repl : LocalTypeR}
    {R : Rel}
    (h_rel : ∀ a b, Bisim a b → R a b)  -- R extends Bisim on branches
    (hWFrepl : LocalTypeR.WellFormed repl)
    (hWFx : LocalTypeR.WellFormed x) (hWFy : LocalTypeR.WellFormed y)
    (hx : UnfoldsToVar x var) (hy : UnfoldsToVar y var) :
    BisimF (RelImage (fun t => t.substitute var repl) R)
           (x.substitute var repl) (y.substitute var repl) := by
  -- Both x.substitute var repl and y.substitute var repl are EQ2-equivalent to repl
  have hxeq : EQ2 (x.substitute var repl) repl :=
    UnfoldsToVar_substitute_EQ2 hx hWFx hWFrepl
  have hyeq : EQ2 (y.substitute var repl) repl :=
    UnfoldsToVar_substitute_EQ2 hy hWFy hWFrepl
  have hWFx_subst : LocalTypeR.WellFormed (x.substitute var repl) :=
    WellFormed_substitute (var := var) hWFx hWFrepl
  have hWFy_subst : LocalTypeR.WellFormed (y.substitute var repl) :=
    WellFormed_substitute (var := var) hWFy hWFrepl
  -- So they're EQ2-equivalent to each other
  have hxyeq : EQ2 (x.substitute var repl) (y.substitute var repl) :=
    EQ2_trans_via_Bisim hxeq (EQ2_symm hyeq) hWFx_subst hWFrepl hWFy_subst
  -- Convert to Bisim
  have hBisim : Bisim (x.substitute var repl) (y.substitute var repl) :=
    EQ2.toBisim hxyeq hWFx_subst hWFy_subst
  obtain ⟨R', hR'post, hxy'⟩ := hBisim
  have hBisimF : BisimF R' (x.substitute var repl) (y.substitute var repl) := hR'post _ _ hxy'
  -- Case on BisimF to determine observable behavior
  cases hBisimF with
  | eq_end hxend hyend =>
    -- Both unfold to end, so BisimF.eq_end applies directly
    exact BisimF.eq_end hxend hyend
  | eq_var hxvar hyvar =>
    -- Both unfold to the same var, so BisimF.eq_var applies directly
    exact BisimF.eq_var hxvar hyvar
  | eq_send hxsend hysend hbr =>
    -- Both can send with R'-related branches bs and cs
    apply BisimF.eq_send hxsend hysend
    -- Need: BranchesRelBisim (RelImage f R) bs cs where f = (fun t => t.substitute var repl)
    -- We have: BranchesRelBisim R' bs cs
    --
    -- Strategy: Since x and y both unfold to var, after substitution they both become
    -- EQ2-equivalent to repl. The branches bs and cs come from repl's structure.
    -- Since both x and y unfold to the same var, their branches are Bisim-related.
    --
    -- Key insight with reflexivity: For any branch b in bs (or cs), since x and y both
    -- unfold to var, the branch b is a "fixed point" of the overall structure.
    -- We can construct RelImage witnesses by taking pre-images = post-images (the branches
    -- themselves), and use reflexivity: R b b.
    --
    -- More precisely: RelImage f R b b = ∃ a a', R a a' ∧ b = f a ∧ b = f a'
    -- We take a = a' = b, and use h_refl to get R b b.
    -- Then we need f b = b, which holds when var is not free in b (the branch is a
    -- fixed point of substitution at var).
    rename_i bs cs
    have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b hr' => ⟨R', hR'post, hr'⟩
    have hbr_bisim : BranchesRelBisim Bisim bs cs :=
      BranchesRelBisim.mono hR'_to_Bisim hbr
    have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2 :=
      WellFormed_branches_of_CanSend hxsend hWFx_subst
    have hWFcs : ∀ lc ∈ cs, LocalTypeR.WellFormed lc.2 :=
      WellFormed_branches_of_CanSend hysend hWFy_subst
    -- Substitution is identity on closed branch continuations
    have hfix_bs : ∀ lb ∈ bs, (lb.2.substitute var repl) = lb.2 := by
      intro lb hmem
      have hclosed : lb.2.isClosed := (hWFbs lb hmem).closed
      have hnotfree : LocalTypeR.isFreeIn var lb.2 = false :=
        LocalTypeR.isFreeIn_false_of_closed lb.2 var hclosed
      exact LocalTypeR.substitute_not_free _ _ _ hnotfree
    have hfix_cs : ∀ lc ∈ cs, (lc.2.substitute var repl) = lc.2 := by
      intro lc hmem
      have hclosed : lc.2.isClosed := (hWFcs lc hmem).closed
      have hnotfree : LocalTypeR.isFreeIn var lc.2 = false :=
        LocalTypeR.isFreeIn_false_of_closed lc.2 var hclosed
      exact LocalTypeR.substitute_not_free _ _ _ hnotfree
    exact BranchesRelBisim_of_Bisim_with_relImage h_rel hbr_bisim hfix_bs hfix_cs
  | eq_recv hxrecv hyrecv hbr =>
    -- Similar to eq_send case
    apply BisimF.eq_recv hxrecv hyrecv
    rename_i bs cs
    have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b hr' => ⟨R', hR'post, hr'⟩
    have hbr_bisim : BranchesRelBisim Bisim bs cs :=
      BranchesRelBisim.mono hR'_to_Bisim hbr
    have hWFbs : ∀ lb ∈ bs, LocalTypeR.WellFormed lb.2 :=
      WellFormed_branches_of_CanRecv hxrecv hWFx_subst
    have hWFcs : ∀ lc ∈ cs, LocalTypeR.WellFormed lc.2 :=
      WellFormed_branches_of_CanRecv hyrecv hWFy_subst
    have hfix_bs : ∀ lb ∈ bs, (lb.2.substitute var repl) = lb.2 := by
      intro lb hmem
      have hclosed : lb.2.isClosed := (hWFbs lb hmem).closed
      have hnotfree : LocalTypeR.isFreeIn var lb.2 = false :=
        LocalTypeR.isFreeIn_false_of_closed lb.2 var hclosed
      exact LocalTypeR.substitute_not_free _ _ _ hnotfree
    have hfix_cs : ∀ lc ∈ cs, (lc.2.substitute var repl) = lc.2 := by
      intro lc hmem
      have hclosed : lc.2.isClosed := (hWFcs lc hmem).closed
      have hnotfree : LocalTypeR.isFreeIn var lc.2 = false :=
        LocalTypeR.isFreeIn_false_of_closed lc.2 var hclosed
      exact LocalTypeR.substitute_not_free _ _ _ hnotfree
    exact BranchesRelBisim_of_Bisim_with_relImage h_rel hbr_bisim hfix_bs hfix_cs


/-- Helper: Bisim can be embedded into RelImage via identity mapping.

    Any Bisim-related pair can be viewed as related through RelImage by taking
    the pre-images to be the same pair (with R = Bisim). -/
private theorem Bisim_to_RelImage (f : LocalTypeR → LocalTypeR) {a b : LocalTypeR}
    (h : Bisim a b) : RelImage f Bisim (f a) (f b) :=
  ⟨a, b, h, rfl, rfl⟩

/-- Lift BranchesRelBisim from R to RelImage f R when R is at least as strong as the images.

    This is useful when we know branches are related by a strong relation R
    and want to show they're related by RelImage f S for some S ⊆ R. -/
private theorem BranchesRelBisim_to_RelImage (f : LocalTypeR → LocalTypeR)
    {R : Rel} {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRelBisim R bs cs)
    (hlift : ∀ a b, R a b → RelImage f R (f a) (f b)) :
    BranchesRelBisim (RelImage f R) (bs.map (fun p => (p.1, f p.2)))
                                     (cs.map (fun p => (p.1, f p.2))) := by
  induction h with
  | nil =>
    simp only [List.map_nil]
    exact List.Forall₂.nil
  | cons hbc hrest ih =>
    simp only [List.map_cons]
    apply List.Forall₂.cons
    · constructor
      · exact hbc.1
      · exact hlift _ _ hbc.2
    · exact ih

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves CanSend.

    Requires Barendregt conditions for the non-shadowed mu case. -/
theorem substitute_preserves_CanSend {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    CanSend (a.substitute var repl) p (bs.map (fun b => (b.1, b.2.substitute var repl))) := by
  refine (CanSend.rec
    (motive := fun a p bs _ =>
      ∀ {var repl}, notBoundAt var a = true →
        (∀ w, isFreeIn w repl = false) →
          CanSend (a.substitute var repl) p
            (bs.map (fun b => (b.1, b.2.substitute var repl))))
    ?base ?mu h) hbar hfresh
  · intro p bs var repl hbar hfresh
    simp only [LocalTypeR.substitute]
    rw [substituteBranches_eq_map]
    exact CanSend.base
  · intro t body p bs h ih var repl hbar hfresh
    simp only [LocalTypeR.substitute]
    split
    · -- t == var is true: substitution is shadowed
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      have hnotfree : isFreeIn t (body.substitute t (.mu t body)) = false :=
        isFreeIn_mu_unfold_false body t
      have hnotfree' : isFreeIn var (body.substitute t (.mu t body)) = false := by
        rw [← htvar]; exact hnotfree
      have hsame : (body.substitute t (.mu t body)).substitute var repl =
                   body.substitute t (.mu t body) :=
        substitute_not_free _ var repl hnotfree'
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) hbar
      have ih' := ih hbar_unfold hfresh
      rw [hsame] at ih'
      exact CanSend.mu ih'
    · -- t == var is false: substitution goes through
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      simp only [notBoundAt] at hbar
      have htne : t ≠ var := fun heq => by simp [heq] at htvar
      have hbne : (var != t) = true := bne_iff_ne.mpr htne.symm
      simp only [hbne, Bool.true_and] at hbar
      have hcomm := subst_mu_comm body var t repl hbar hfresh htne
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hbne, hbar])
      have ih' := ih hbar_unfold hfresh
      rw [← hcomm] at ih'
      exact CanSend.mu ih'

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves CanRecv.

    Requires Barendregt conditions for the non-shadowed mu case. -/
theorem substitute_preserves_CanRecv {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    CanRecv (a.substitute var repl) p (bs.map (fun b => (b.1, b.2.substitute var repl))) := by
  -- Reduce recv to send via duality, then transport Barendregt conditions.
  have hsend : CanSend a.dual p (LocalTypeR.dualBranches bs) := CanRecv.dual h
  have hbar_dual : notBoundAt var a.dual = true := by
    simpa [notBoundAt_dual] using hbar
  have hfresh_dual : ∀ w, isFreeIn w repl.dual = false := by
    intro w
    simpa [isFreeIn_dual] using hfresh w
  have hsend_subst :=
    substitute_preserves_CanSend (a := a.dual) (repl := repl.dual)
      (bs := LocalTypeR.dualBranches bs) hsend hbar_dual hfresh_dual
  have hsend' :
      CanSend (a.substitute var repl).dual p
        (LocalTypeR.dualBranches (bs.map (fun b => (b.1, b.2.substitute var repl)))) := by
    -- Commute dual with substitution on types and branches.
    have hbranches :
        (LocalTypeR.dualBranches bs).map (fun b => (b.1, b.2.substitute var repl.dual)) =
          LocalTypeR.dualBranches (bs.map (fun b => (b.1, b.2.substitute var repl))) := by
      calc
        (LocalTypeR.dualBranches bs).map (fun b => (b.1, b.2.substitute var repl.dual))
            = LocalTypeR.substituteBranches (LocalTypeR.dualBranches bs) var repl.dual := by
                simp [substituteBranches_eq_map]
        _ = LocalTypeR.dualBranches (LocalTypeR.substituteBranches bs var repl) := by
                simpa using (dualBranches_substituteBranches bs var repl).symm
        _ = LocalTypeR.dualBranches (bs.map (fun b => (b.1, b.2.substitute var repl))) := by
                simp [substituteBranches_eq_map]
    simpa [LocalTypeR.dual_substitute, hbranches] using hsend_subst
  have hrecv := CanSend.dual hsend'
  simpa [LocalTypeR.dual_dual, dualBranches_dualBranches] using hrecv

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution is compatible (preserves BisimF structure) under Barendregt convention.

    This is the key lemma for proving EQ2_substitute.

    Requires Barendregt conditions:
    - `notBoundAt var x = true` and `notBoundAt var y = true`: var is not used as a binder
    - `∀ w, isFreeIn w repl = false`: replacement term is closed

    Note: These conditions are satisfied by well-formed types in practice. -/
theorem substitute_compatible_barendregt (var : String) (repl : LocalTypeR)
    (hfresh : ∀ w, isFreeIn w repl = false) (hWFrepl : LocalTypeR.WellFormed repl) :
    ∀ R x y, (∀ a b, Bisim a b → R a b) → BisimF R x y →
      LocalTypeR.WellFormed x → LocalTypeR.WellFormed y →
      notBoundAt var x = true → notBoundAt var y = true →
      BisimF (RelImage (fun t => t.substitute var repl) R)
             (x.substitute var repl) (y.substitute var repl) := by
  intro R x y h_rel hBisimF hWFx hWFy hbar_x hbar_y
  cases hBisimF with
  | eq_end hx hy =>
    -- Both unfold to end - use Barendregt version which gives direct result
    have hx' := substitute_preserves_UnfoldsToEnd_barendregt hx hbar_x hfresh
    have hy' := substitute_preserves_UnfoldsToEnd_barendregt hy hbar_y hfresh
    exact BisimF.eq_end hx' hy'
  | eq_var hx hy =>
    -- Both unfold to same var v
    -- After substitution: if v ≠ var, still unfolds to v; if v = var, unfolds to repl
    rename_i v
    by_cases heq : v = var
    · -- Case: v = var, both become repl after substitution
      -- Use substitute_at_var_bisimF with Bisim reflexivity
      have hx_eq : UnfoldsToVar x var := heq ▸ hx
      have hy_eq : UnfoldsToVar y var := heq ▸ hy
      exact substitute_at_var_bisimF (R := R) h_rel hWFrepl hWFx hWFy hx_eq hy_eq
    · -- Case: v ≠ var, both still unfold to v after substitution
      have hx' := substitute_preserves_UnfoldsToVar hx heq hbar_x hfresh
      have hy' := substitute_preserves_UnfoldsToVar hy heq hbar_y hfresh
      exact BisimF.eq_var hx' hy'
  | eq_send hx hy hbr =>
    -- Both can send with R-related branches
    have hx' := substitute_preserves_CanSend hx hbar_x hfresh
    have hy' := substitute_preserves_CanSend hy hbar_y hfresh
    apply BisimF.eq_send hx' hy'
    -- Need: BranchesRelBisim (RelImage substitute R) mapped_bs mapped_cs
    exact BranchesRelBisim.map_image hbr
  | eq_recv hx hy hbr =>
    have hx' := substitute_preserves_CanRecv hx hbar_x hfresh
    have hy' := substitute_preserves_CanRecv hy hbar_y hfresh
    apply BisimF.eq_recv hx' hy'
    exact BranchesRelBisim.map_image hbr

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- EQ2 is preserved by substitution (Barendregt version).

    This version is proven via the Barendregt commutation proof in
    `SubstCommBarendregt.lean` and removes the DB bridge assumption. -/
theorem EQ2_substitute_via_Bisim {a b : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : EQ2 a b)
    (hbarA : notBoundAt var a = true)
    (hbarB : notBoundAt var b = true)
    (hfresh : ∀ t, isFreeIn t repl = false)
    (hnomu : ∀ t body, repl ≠ .mu t body) :
    EQ2 (a.substitute var repl) (b.substitute var repl) := by
  exact EQ2_substitute_barendregt a b var repl h hbarA hbarB hfresh hnomu

end RumpsteakV2.Protocol.CoTypes.Bisim
