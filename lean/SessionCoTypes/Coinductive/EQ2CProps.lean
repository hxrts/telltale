import Mathlib
import SessionCoTypes.Coinductive.EQ2C
import SessionCoTypes.Coinductive.WellFormed

set_option linter.dupNamespace false

/-! # EQ2C Properties

Lemmas for EQ2C interaction with constructors and mu-unfolding. -/

/-
The Problem. EQ2C is defined abstractly via existentially quantified bisimulation,
but proofs need concrete lemmas for constructors (end, var, send, recv, mu) and
unfolding. Constructing bisimulations that account for unfolding is non-trivial.

Solution Structure. Base cases (eq2_c_end, eq2_c_var) establish reflexivity at terminals.
EQ2C_mkVar_left/right_unfolds extract unfolding witnesses. eq2_c_send/recv give
congruence for communication. eq2_c_unfold_left/right allow mu-wrapping on either
side. observable_rel_c_mu_left/right lift observable relations through mu.
-/

namespace SessionCoTypes.Coinductive

/-! ## Local helpers (dest equality / mu eta) -/

private lemma eq_of_dest_eq {a b : LocalTypeC} (h : PFunctor.M.dest a = PFunctor.M.dest b) :
    a = b := by
  refine PFunctor.M.bisim (R := fun x y => PFunctor.M.dest x = PFunctor.M.dest y) ?_ a b h
  intro x y hxy
  cases hx : x.dest with
  | mk a f =>
      have hy : y.dest = ⟨a, f⟩ := by
        simpa [hx] using hxy.symm
      refine ⟨a, f, f, rfl, hy, ?_⟩
      intro i
      rfl

private lemma mu_eta {b : LocalTypeC} {x : String} {k : Unit → LocalTypeC}
    (hdest : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, k⟩) : b = mkMu x (k ()) := by
  have hk : k = fun _ => k () := by
    funext u
    cases u
    rfl
  have hdest' : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, fun _ => k ()⟩ := by
    have hdest' := hdest
    rw [hk] at hdest'
    exact hdest'
  exact eq_of_dest_eq hdest'

/-! ## Variable unfolding utilities -/

lemma unfolds_to_c_mk_var {x : String} {u : LocalTypeC}
    (h : UnfoldsToC (mkVar x) u) : u = mkVar x := by
  cases (Relation.ReflTransGen.cases_head h) with
  | inl heq => exact heq.symm
  | inr hexists =>
      rcases hexists with ⟨y, hstep, _⟩
      rcases hstep with ⟨x', f, hdest, _⟩
      simp only [mkVar, PFunctor.M.dest_mk] at hdest
      injection hdest with h1 _
      cases h1

lemma unfolds_to_var_c_mk_var {x v : String} (h : UnfoldsToVarC (mkVar x) v) : v = x := by
  rcases h with ⟨u, hsteps, hhead⟩
  have hu : u = mkVar x := unfolds_to_c_mk_var hsteps
  subst hu
  simp [head_mk_var] at hhead
  exact hhead.symm

/-! ## Base cases: end and var -/

/-- Base EQ2C proof for `end`. -/
lemma eq2_c_end : EQ2C mkEnd mkEnd := by
  let R : LocalTypeC → LocalTypeC → Prop := fun a b => a = mkEnd ∧ b = mkEnd
  have hR : IsBisimulationC R := by
    intro a b hrel
    rcases hrel with ⟨ha, hb⟩
    subst ha; subst hb
    have obs : ObservableC mkEnd := observable_mk_end
    have hend : UnfoldsToEndC mkEnd := ⟨mkEnd, Relation.ReflTransGen.refl, head_mk_end⟩
    exact ⟨obs, obs, ObservableRelC.is_end hend hend⟩
  exact ⟨R, hR, ⟨rfl, rfl⟩⟩

/-- Base EQ2C proof for variables. -/
lemma eq2_c_var (v : String) : EQ2C (mkVar v) (mkVar v) := by
  let R : LocalTypeC → LocalTypeC → Prop := fun a b => a = mkVar v ∧ b = mkVar v
  have hR : IsBisimulationC R := by
    intro a b hrel
    rcases hrel with ⟨ha, hb⟩
    subst ha; subst hb
    have obs : ObservableC (mkVar v) := observable_mk_var v
    have hvar : UnfoldsToVarC (mkVar v) v := ⟨mkVar v, Relation.ReflTransGen.refl, head_mk_var v⟩
    exact ⟨obs, obs, ObservableRelC.is_var v hvar hvar⟩
  exact ⟨R, hR, ⟨rfl, rfl⟩⟩

/-! ## Extracting unfold witnesses from EQ2C -/

lemma eq2_c_mk_var_left_unfolds {x : String} {b : LocalTypeC}
    (h : EQ2C (mkVar x) b) : UnfoldsToVarC b x := by
  rcases h with ⟨R, hR, hrel⟩
  obtain ⟨obs_a, obs_b, hobs⟩ := hR _ _ hrel
  -- obs_a : ObservableC (mkVar x). Since mkVar x has head var x, the only possibility is is_var.
  cases hobs with
  | is_var v ha hb =>
      -- ha : UnfoldsToVarC (mkVar x) v, so v = x
      have hv : v = x := unfolds_to_var_c_mk_var ha
      subst hv
      exact hb
  | is_end ha _ =>
      rcases ha with ⟨u, hsteps, hhead⟩
      have hu : u = mkVar x := unfolds_to_c_mk_var hsteps
      subst hu
      simp [head_mk_var] at hhead
  | is_send p _ _ ha _ _ =>
      rcases ha with ⟨u, labels, hsteps, hhead, _⟩
      have hu : u = mkVar x := unfolds_to_c_mk_var hsteps
      subst hu
      simp [head_mk_var] at hhead
  | is_recv p _ _ ha _ _ =>
      rcases ha with ⟨u, labels, hsteps, hhead, _⟩
      have hu : u = mkVar x := unfolds_to_c_mk_var hsteps
      subst hu
      simp [head_mk_var] at hhead

lemma eq2_c_mk_var_right_unfolds {x : String} {a : LocalTypeC}
    (h : EQ2C a (mkVar x)) : UnfoldsToVarC a x := by
  have h' : EQ2C (mkVar x) a := eq2_c_symm h
  exact eq2_c_mk_var_left_unfolds h'

/-! ## Observable step from EQ2C -/

lemma eq2_c_observable_rel {a b : LocalTypeC} (h : EQ2C a b) :
    ∃ _ : ObservableC a, ∃ _ : ObservableC b, ObservableRelC EQ2C a b := by
  rcases h with ⟨R, hR, hab⟩
  obtain ⟨obs_a, obs_b, hrel⟩ := hR _ _ hab
  -- Any bisimulation witness is contained in EQ2C by definition.
  have hR_le : R ≤ EQ2C := fun x y hxy => ⟨R, hR, hxy⟩
  exact ⟨obs_a, obs_b, observable_rel_c_mono hR_le hrel⟩

/-! ## Communication congruence -/

/-- EQ2C is closed under send, given branch-wise EQ2C. -/
lemma eq2_c_send {p : String} {bs cs : List (Label × LocalTypeC)}
    (hbr : BranchesRelC EQ2C bs cs) : EQ2C (mkSend p bs) (mkSend p cs) := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun a b => (a = mkSend p bs ∧ b = mkSend p cs) ∨ EQ2C a b
  have hR' : IsBisimulationC R' := by
    intro a b hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_a, obs_b, hobs⟩ := hR a b hrel
        have hobs' : ObservableRelC R' a b :=
          observable_rel_c_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        have obs_a : ObservableC (mkSend p bs) := observable_mk_send p bs
        have obs_b : ObservableC (mkSend p cs) := observable_mk_send p cs
        have hbr' : BranchesRelC R' bs cs :=
          branches_rel_c_mono (fun _ _ hr => Or.inr hr) hbr
        -- Construct the CanSendC proofs directly
        have ha_send : CanSendC (mkSend p bs) p bs :=
          ⟨mkSend p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, head_mk_send p bs, (branches_of_mk_send p bs).symm⟩
        have hb_send : CanSendC (mkSend p cs) p cs :=
          ⟨mkSend p cs, cs.map Prod.fst, Relation.ReflTransGen.refl, head_mk_send p cs, (branches_of_mk_send p cs).symm⟩
        exact ⟨obs_a, obs_b, ObservableRelC.is_send p bs cs ha_send hb_send hbr'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- EQ2C is closed under recv, given branch-wise EQ2C.
    Communication congruence: recv case. -/

/-! ### Recv Congruence -/

lemma eq2_c_recv {p : String} {bs cs : List (Label × LocalTypeC)}
    (hbr : BranchesRelC EQ2C bs cs) : EQ2C (mkRecv p bs) (mkRecv p cs) := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun a b => (a = mkRecv p bs ∧ b = mkRecv p cs) ∨ EQ2C a b
  have hR' : IsBisimulationC R' := by
    intro a b hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_a, obs_b, hobs⟩ := hR a b hrel
        have hobs' : ObservableRelC R' a b :=
          observable_rel_c_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        have obs_a : ObservableC (mkRecv p bs) := observable_mk_recv p bs
        have obs_b : ObservableC (mkRecv p cs) := observable_mk_recv p cs
        have hbr' : BranchesRelC R' bs cs :=
          branches_rel_c_mono (fun _ _ hr => Or.inr hr) hbr
        -- Construct the CanRecvC proofs directly
        have ha_recv : CanRecvC (mkRecv p bs) p bs :=
          ⟨mkRecv p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, head_mk_recv p bs, (branches_of_mk_recv p bs).symm⟩
        have hb_recv : CanRecvC (mkRecv p cs) p cs :=
          ⟨mkRecv p cs, cs.map Prod.fst, Relation.ReflTransGen.refl, head_mk_recv p cs, (branches_of_mk_recv p cs).symm⟩
        exact ⟨obs_a, obs_b, ObservableRelC.is_recv p bs cs ha_recv hb_recv hbr'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-! ## Mu-unfolding congruence -/

/-- Wrap a bisimulation on the left with a μ constructor. -/
lemma eq2_c_unfold_left {t u : LocalTypeC} (h : EQ2C t u) (x : String) :
    EQ2C (mkMu x t) u := by
  rcases h with ⟨R, hR, htu⟩
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun a b => (a = mkMu x t ∧ b = u) ∨ R a b
  have hR' : IsBisimulationC R' := by
    intro a b hrel
    cases hrel with
    | inr hRrel =>
        obtain ⟨obs_a, obs_b, hobs⟩ := hR a b hRrel
        have hobs' : ObservableRelC R' a b :=
          observable_rel_c_mono (fun _ _ hr => Or.inr hr) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hbeq⟩
        subst ha
        -- hbeq : b = u, so rewrite using it rather than subst (avoids scoping issues with param u)
        obtain ⟨obs_t, obs_u, hobs⟩ := hR t u htu
        -- Lift the observable on `t` to `mkMu x t`.
        have obs_mu : ObservableC (mkMu x t) := observable_mk_mu obs_t
        -- obs_b for b comes from obs_u via the equality
        have obs_b : ObservableC b := hbeq ▸ obs_u
        -- The key step: mkMu x t unfolds to t in one step
        have hstep : UnfoldsC (mkMu x t) t := by
          refine ⟨x, fun _ => t, ?_, rfl⟩
          simp [mkMu]
        -- Build the corresponding observable relation.
        have hrel' : ObservableRelC R' (mkMu x t) b := by
          subst hbeq  -- Now b is replaced with u in the goal
          cases hobs with
          | is_end ht hu =>
              -- Lift UnfoldsToEndC through mu
              rcases ht with ⟨ut, hsteps_t, hhead_t⟩
              have hmu : UnfoldsToEndC (mkMu x t) :=
                ⟨ut, Relation.ReflTransGen.head hstep hsteps_t, hhead_t⟩
              exact ObservableRelC.is_end hmu hu
          | is_var v ht hu =>
              -- Lift UnfoldsToVarC through mu
              rcases ht with ⟨ut, hsteps_t, hhead_t⟩
              have hmu : UnfoldsToVarC (mkMu x t) v :=
                ⟨ut, Relation.ReflTransGen.head hstep hsteps_t, hhead_t⟩
              exact ObservableRelC.is_var v hmu hu
          | is_send p bs cs ht hu hbr =>
              -- Lift CanSendC through mu
              rcases ht with ⟨ut, labels, hsteps_t, hhead_t, hbs⟩
              have hmu : CanSendC (mkMu x t) p bs :=
                ⟨ut, labels, Relation.ReflTransGen.head hstep hsteps_t, hhead_t, hbs⟩
              exact ObservableRelC.is_send p bs cs hmu hu
                (branches_rel_c_mono (fun _ _ hr => Or.inr hr) hbr)
          | is_recv p bs cs ht hu hbr =>
              -- Lift CanRecvC through mu
              rcases ht with ⟨ut, labels, hsteps_t, hhead_t, hbs⟩
              have hmu : CanRecvC (mkMu x t) p bs :=
                ⟨ut, labels, Relation.ReflTransGen.head hstep hsteps_t, hhead_t, hbs⟩
              exact ObservableRelC.is_recv p bs cs hmu hu
                (branches_rel_c_mono (fun _ _ hr => Or.inr hr) hbr)
        exact ⟨obs_mu, obs_b, hrel'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- Wrap a bisimulation on the right with a μ constructor.
    Mu-unfolding congruence: right wrapper. -/

/-! ### Right Mu Wrapper -/

lemma eq2_c_unfold_right {t u : LocalTypeC} (h : EQ2C t u) (x : String) :
    EQ2C t (mkMu x u) := by
  have h' : EQ2C u t := eq2_c_symm h
  have h'' : EQ2C (mkMu x u) t := eq2_c_unfold_left h' x
  exact eq2_c_symm h''

/-! ## ObservableRelC lifting through mu -/

lemma observable_rel_c_mu_left {R : LocalTypeC → LocalTypeC → Prop} {x : String}
    {t u : LocalTypeC} (hrel : ObservableRelC R t u) :
    ObservableRelC R (mkMu x t) u := by
  -- one-step unfold: mkMu x t ↠ t
  have hstep : UnfoldsC (mkMu x t) t := by
    refine ⟨x, fun _ => t, ?_, rfl⟩
    simp [mkMu]
  cases hrel with
  | is_end ht hu =>
      rcases ht with ⟨ut, hsteps_t, hhead_t⟩
      have hmu : UnfoldsToEndC (mkMu x t) :=
        ⟨ut, Relation.ReflTransGen.head hstep hsteps_t, hhead_t⟩
      exact ObservableRelC.is_end hmu hu
  | is_var v ht hu =>
      rcases ht with ⟨ut, hsteps_t, hhead_t⟩
      have hmu : UnfoldsToVarC (mkMu x t) v :=
        ⟨ut, Relation.ReflTransGen.head hstep hsteps_t, hhead_t⟩
      exact ObservableRelC.is_var v hmu hu
  | is_send p bs cs ht hu hbr =>
      rcases ht with ⟨ut, labels, hsteps_t, hhead_t, hbs⟩
      have hmu : CanSendC (mkMu x t) p bs :=
        ⟨ut, labels, Relation.ReflTransGen.head hstep hsteps_t, hhead_t, hbs⟩
      exact ObservableRelC.is_send p bs cs hmu hu hbr
  | is_recv p bs cs ht hu hbr =>
      rcases ht with ⟨ut, labels, hsteps_t, hhead_t, hbs⟩
      have hmu : CanRecvC (mkMu x t) p bs :=
        ⟨ut, labels, Relation.ReflTransGen.head hstep hsteps_t, hhead_t, hbs⟩
      exact ObservableRelC.is_recv p bs cs hmu hu hbr

/-! ## ObservableRelC lifting through mu: right side -/

lemma observable_rel_c_mu_right {R : LocalTypeC → LocalTypeC → Prop} {x : String}
    {t u : LocalTypeC} (hrel : ObservableRelC R t u) :
    ObservableRelC R t (mkMu x u) := by
  -- one-step unfold: mkMu x u ↠ u
  have hstep : UnfoldsC (mkMu x u) u := by
    refine ⟨x, fun _ => u, ?_, rfl⟩
    simp [mkMu]
  cases hrel with
  | is_end ht hu =>
      rcases hu with ⟨uu, hsteps_u, hhead_u⟩
      have hmu : UnfoldsToEndC (mkMu x u) :=
        ⟨uu, Relation.ReflTransGen.head hstep hsteps_u, hhead_u⟩
      exact ObservableRelC.is_end ht hmu
  | is_var v ht hu =>
      rcases hu with ⟨uu, hsteps_u, hhead_u⟩
      have hmu : UnfoldsToVarC (mkMu x u) v :=
        ⟨uu, Relation.ReflTransGen.head hstep hsteps_u, hhead_u⟩
      exact ObservableRelC.is_var v ht hmu
  | is_send p bs cs ht hu hbr =>
      rcases hu with ⟨uu, labels, hsteps_u, hhead_u, hcs⟩
      have hmu : CanSendC (mkMu x u) p cs :=
        ⟨uu, labels, Relation.ReflTransGen.head hstep hsteps_u, hhead_u, hcs⟩
      exact ObservableRelC.is_send p bs cs ht hmu hbr
  | is_recv p bs cs ht hu hbr =>
      rcases hu with ⟨uu, labels, hsteps_u, hhead_u, hcs⟩
      have hmu : CanRecvC (mkMu x u) p cs :=
        ⟨uu, labels, Relation.ReflTransGen.head hstep hsteps_u, hhead_u, hcs⟩
      exact ObservableRelC.is_recv p bs cs ht hmu hbr

/-! ## ObservableRelC stability under μ-unfolding -/

lemma observable_rel_c_unfolds_c_left {R : LocalTypeC → LocalTypeC → Prop}
    {a a' b : LocalTypeC} (hstep : UnfoldsC a a') (hrel : ObservableRelC R a' b) :
    ObservableRelC R a b := by
  rcases hstep with ⟨x, f, hdest, rfl⟩
  have ha : a = mkMu x (f ()) := mu_eta (b := a) (x := x) (k := f) hdest
  have hrel' : ObservableRelC R (mkMu x (f ())) b := observable_rel_c_mu_left (x := x) hrel
  simpa [ha] using hrel'


lemma observable_rel_c_unfolds_c_right {R : LocalTypeC → LocalTypeC → Prop}
    {a b b' : LocalTypeC} (hstep : UnfoldsC b b') (hrel : ObservableRelC R a b') :
    ObservableRelC R a b := by
  rcases hstep with ⟨x, f, hdest, rfl⟩
  have hb : b = mkMu x (f ()) := mu_eta (b := b) (x := x) (k := f) hdest
  have hrel' : ObservableRelC R a (mkMu x (f ())) := observable_rel_c_mu_right (x := x) hrel
  simpa [hb] using hrel'


lemma observable_rel_c_unfolds_to_left {R : LocalTypeC → LocalTypeC → Prop}
    {a a' b : LocalTypeC} (hsteps : UnfoldsToC a a') (hrel : ObservableRelC R a' b) :
    ObservableRelC R a b := by
  induction hsteps generalizing b with
  | refl => exact hrel
  | tail hsteps hstep ih =>
      have hrel' : ObservableRelC R _ b := observable_rel_c_unfolds_c_left hstep hrel
      exact ih hrel'

lemma observable_rel_c_unfolds_to_right {R : LocalTypeC → LocalTypeC → Prop}
    {a b b' : LocalTypeC} (hsteps : UnfoldsToC b b') (hrel : ObservableRelC R a b') :
    ObservableRelC R a b := by
  induction hsteps generalizing a with
  | refl => exact hrel
  | tail hsteps hstep ih =>
      have hrel' : ObservableRelC R a _ := observable_rel_c_unfolds_c_right hstep hrel
      exact ih hrel'

/-! ## ObservableRelC inversion through μ-unfolding -/

private lemma unfolds_c_right_unique : Relator.RightUnique UnfoldsC := by
  intro a b c hab hac
  rcases hab with ⟨x, f, hdest, rfl⟩
  rcases hac with ⟨y, g, hdest', rfl⟩
  have hpair :
      (⟨LocalTypeHead.mu x, f⟩ : LocalTypeF LocalTypeC) =
        ⟨LocalTypeHead.mu y, g⟩ := by
    exact hdest.symm.trans hdest'
  cases hpair
  rfl

private lemma unfolds_to_c_tail_of_step {a a' u : LocalTypeC}
    (hstep : UnfoldsC a a') (hunf : UnfoldsToC a u)
    (hnomu : ¬ (∃ x, head u = .mu x)) : UnfoldsToC a' u := by
  rcases Relation.ReflTransGen.cases_head hunf with (hEq | hstep')
  · -- refl: u = a, but a is mu by hstep, contradiction with hnomu
    subst hEq
    rcases hstep with ⟨x, f, hdest, rfl⟩
    have hmu : head a = .mu x := by
      simp [head, hdest]
    exact (hnomu ⟨x, hmu⟩).elim
  · rcases hstep' with ⟨c, hstep', hrest⟩
    have hc : c = a' := by
      exact unfolds_c_right_unique hstep' hstep
    subst hc
    exact hrest

/-! ## ObservableRelC inversion through μ-unfolding: left inversion -/

lemma observable_rel_c_unfolds_c_left_inv {R : LocalTypeC → LocalTypeC → Prop}
    {a a' b : LocalTypeC} (hstep : UnfoldsC a a') (hrel : ObservableRelC R a b) :
    ObservableRelC R a' b := by
  cases hrel with
  | is_end ha hb =>
      rcases ha with ⟨u, hunf, hhead⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC a' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_end ⟨u, hunf', hhead⟩ hb
  | is_var v ha hb =>
      rcases ha with ⟨u, hunf, hhead⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC a' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_var v ⟨u, hunf', hhead⟩ hb
  | is_send p bs cs ha hb hbr =>
      rcases ha with ⟨u, labels, hunf, hhead, hbs⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC a' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_send p bs cs ⟨u, labels, hunf', hhead, hbs⟩ hb hbr
  | is_recv p bs cs ha hb hbr =>
      rcases ha with ⟨u, labels, hunf, hhead, hbs⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC a' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_recv p bs cs ⟨u, labels, hunf', hhead, hbs⟩ hb hbr

/-! ## ObservableRelC inversion through μ-unfolding: right inversion -/

lemma observable_rel_c_unfolds_c_right_inv {R : LocalTypeC → LocalTypeC → Prop}
    {a b b' : LocalTypeC} (hstep : UnfoldsC b b') (hrel : ObservableRelC R a b) :
    ObservableRelC R a b' := by
  cases hrel with
  | is_end ha hb =>
      rcases hb with ⟨u, hunf, hhead⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC b' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_end ha ⟨u, hunf', hhead⟩
  | is_var v ha hb =>
      rcases hb with ⟨u, hunf, hhead⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC b' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_var v ha ⟨u, hunf', hhead⟩
  | is_send p bs cs ha hb hbr =>
      rcases hb with ⟨u, labels, hunf, hhead, hbs⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC b' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_send p bs cs ha ⟨u, labels, hunf', hhead, hbs⟩ hbr
  | is_recv p bs cs ha hb hbr =>
      rcases hb with ⟨u, labels, hunf, hhead, hbs⟩
      have hnomu : ¬ (∃ x, head u = .mu x) := by simp [hhead]
      have hunf' : UnfoldsToC b' u := unfolds_to_c_tail_of_step hstep hunf hnomu
      exact ObservableRelC.is_recv p bs cs ha ⟨u, labels, hunf', hhead, hbs⟩ hbr

end SessionCoTypes.Coinductive
