import Mathlib
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.WellFormed

set_option linter.dupNamespace false

/-
The Problem. EQ2C is defined as an existentially quantified bisimulation, but
practical proofs need lemmas showing how EQ2C interacts with smart constructors
and mu-unfolding.

The difficulty is that mu-unfolding on one side of an EQ2C relation requires
constructing a new bisimulation that accounts for the unfolding step. Similarly,
congruence for send/recv requires lifting branch-wise EQ2C to the full type.

Solution Structure.
1. Base cases: EQ2C_end and EQ2C_var establish reflexivity at terminals
2. EQ2C_mkVar_left/right_unfolds extract the unfolding witness from EQ2C
3. EQ2C_send and EQ2C_recv give congruence for communication types
4. EQ2C_unfold_left/right allow mu-wrapping on either side
5. ObservableRelC_mu_left/right lift observable relations through mu
-/

namespace RumpsteakV2.Coinductive

/-! ## Variable unfolding utilities -/

lemma unfoldsToC_mkVar {x : String} {u : LocalTypeC}
    (h : UnfoldsToC (mkVar x) u) : u = mkVar x := by
  cases (Relation.ReflTransGen.cases_head h) with
  | inl heq => exact heq.symm
  | inr hexists =>
      rcases hexists with ⟨y, hstep, _⟩
      rcases hstep with ⟨x', f, hdest, _⟩
      simp only [mkVar, PFunctor.M.dest_mk] at hdest
      injection hdest with h1 _
      cases h1

lemma unfoldsToVarC_mkVar {x v : String} (h : UnfoldsToVarC (mkVar x) v) : v = x := by
  rcases h with ⟨u, hsteps, hhead⟩
  have hu : u = mkVar x := unfoldsToC_mkVar hsteps
  subst hu
  simp [head_mkVar] at hhead
  exact hhead.symm

/-! ## Base cases: end and var -/

/-- Base EQ2C proof for `end`. -/
lemma EQ2C_end : EQ2C mkEnd mkEnd := by
  let R : LocalTypeC → LocalTypeC → Prop := fun a b => a = mkEnd ∧ b = mkEnd
  have hR : IsBisimulationC R := by
    intro a b hrel
    rcases hrel with ⟨ha, hb⟩
    subst ha; subst hb
    have obs : ObservableC mkEnd := observable_mkEnd
    have hend : UnfoldsToEndC mkEnd := ⟨mkEnd, Relation.ReflTransGen.refl, head_mkEnd⟩
    exact ⟨obs, obs, ObservableRelC.is_end hend hend⟩
  exact ⟨R, hR, ⟨rfl, rfl⟩⟩

/-- Base EQ2C proof for variables. -/
lemma EQ2C_var (v : String) : EQ2C (mkVar v) (mkVar v) := by
  let R : LocalTypeC → LocalTypeC → Prop := fun a b => a = mkVar v ∧ b = mkVar v
  have hR : IsBisimulationC R := by
    intro a b hrel
    rcases hrel with ⟨ha, hb⟩
    subst ha; subst hb
    have obs : ObservableC (mkVar v) := observable_mkVar v
    have hvar : UnfoldsToVarC (mkVar v) v := ⟨mkVar v, Relation.ReflTransGen.refl, head_mkVar v⟩
    exact ⟨obs, obs, ObservableRelC.is_var v hvar hvar⟩
  exact ⟨R, hR, ⟨rfl, rfl⟩⟩

/-! ## Extracting unfold witnesses from EQ2C -/

lemma EQ2C_mkVar_left_unfolds {x : String} {b : LocalTypeC}
    (h : EQ2C (mkVar x) b) : UnfoldsToVarC b x := by
  rcases h with ⟨R, hR, hrel⟩
  obtain ⟨obs_a, obs_b, hobs⟩ := hR _ _ hrel
  -- obs_a : ObservableC (mkVar x). Since mkVar x has head var x, the only possibility is is_var.
  cases hobs with
  | is_var v ha hb =>
      -- ha : UnfoldsToVarC (mkVar x) v, so v = x
      have hv : v = x := unfoldsToVarC_mkVar ha
      subst hv
      exact hb
  | is_end ha _ =>
      rcases ha with ⟨u, hsteps, hhead⟩
      have hu : u = mkVar x := unfoldsToC_mkVar hsteps
      subst hu
      simp [head_mkVar] at hhead
  | is_send p _ _ ha _ _ =>
      rcases ha with ⟨u, labels, hsteps, hhead, _⟩
      have hu : u = mkVar x := unfoldsToC_mkVar hsteps
      subst hu
      simp [head_mkVar] at hhead
  | is_recv p _ _ ha _ _ =>
      rcases ha with ⟨u, labels, hsteps, hhead, _⟩
      have hu : u = mkVar x := unfoldsToC_mkVar hsteps
      subst hu
      simp [head_mkVar] at hhead

lemma EQ2C_mkVar_right_unfolds {x : String} {a : LocalTypeC}
    (h : EQ2C a (mkVar x)) : UnfoldsToVarC a x := by
  have h' : EQ2C (mkVar x) a := EQ2C_symm h
  exact EQ2C_mkVar_left_unfolds h'

/-! ## Communication congruence -/

/-- EQ2C is closed under send, given branch-wise EQ2C. -/
lemma EQ2C_send {p : String} {bs cs : List (Label × LocalTypeC)}
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
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        have obs_a : ObservableC (mkSend p bs) := observable_mkSend p bs
        have obs_b : ObservableC (mkSend p cs) := observable_mkSend p cs
        have hbr' : BranchesRelC R' bs cs :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        -- Construct the CanSendC proofs directly
        have ha_send : CanSendC (mkSend p bs) p bs :=
          ⟨mkSend p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, head_mkSend p bs, (branchesOf_mkSend p bs).symm⟩
        have hb_send : CanSendC (mkSend p cs) p cs :=
          ⟨mkSend p cs, cs.map Prod.fst, Relation.ReflTransGen.refl, head_mkSend p cs, (branchesOf_mkSend p cs).symm⟩
        exact ⟨obs_a, obs_b, ObservableRelC.is_send p bs cs ha_send hb_send hbr'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- EQ2C is closed under recv, given branch-wise EQ2C. -/
lemma EQ2C_recv {p : String} {bs cs : List (Label × LocalTypeC)}
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
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hb⟩
        subst ha; subst hb
        have obs_a : ObservableC (mkRecv p bs) := observable_mkRecv p bs
        have obs_b : ObservableC (mkRecv p cs) := observable_mkRecv p cs
        have hbr' : BranchesRelC R' bs cs :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        -- Construct the CanRecvC proofs directly
        have ha_recv : CanRecvC (mkRecv p bs) p bs :=
          ⟨mkRecv p bs, bs.map Prod.fst, Relation.ReflTransGen.refl, head_mkRecv p bs, (branchesOf_mkRecv p bs).symm⟩
        have hb_recv : CanRecvC (mkRecv p cs) p cs :=
          ⟨mkRecv p cs, cs.map Prod.fst, Relation.ReflTransGen.refl, head_mkRecv p cs, (branchesOf_mkRecv p cs).symm⟩
        exact ⟨obs_a, obs_b, ObservableRelC.is_recv p bs cs ha_recv hb_recv hbr'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-! ## Mu-unfolding congruence -/

/-- Wrap a bisimulation on the left with a μ constructor. -/
lemma EQ2C_unfold_left {t u : LocalTypeC} (h : EQ2C t u) (x : String) :
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
          ObservableRelC_mono (fun _ _ hr => Or.inr hr) hobs
        exact ⟨obs_a, obs_b, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨ha, hbeq⟩
        subst ha
        -- hbeq : b = u, so rewrite using it rather than subst (avoids scoping issues with param u)
        obtain ⟨obs_t, obs_u, hobs⟩ := hR t u htu
        -- Lift the observable on `t` to `mkMu x t`.
        have obs_mu : ObservableC (mkMu x t) := observable_mkMu obs_t
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
                (BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr)
          | is_recv p bs cs ht hu hbr =>
              -- Lift CanRecvC through mu
              rcases ht with ⟨ut, labels, hsteps_t, hhead_t, hbs⟩
              have hmu : CanRecvC (mkMu x t) p bs :=
                ⟨ut, labels, Relation.ReflTransGen.head hstep hsteps_t, hhead_t, hbs⟩
              exact ObservableRelC.is_recv p bs cs hmu hu
                (BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr)
        exact ⟨obs_mu, obs_b, hrel'⟩
  refine ⟨R', hR', ?_⟩
  exact Or.inl ⟨rfl, rfl⟩

/-- Wrap a bisimulation on the right with a μ constructor. -/
lemma EQ2C_unfold_right {t u : LocalTypeC} (h : EQ2C t u) (x : String) :
    EQ2C t (mkMu x u) := by
  have h' : EQ2C u t := EQ2C_symm h
  have h'' : EQ2C (mkMu x u) t := EQ2C_unfold_left h' x
  exact EQ2C_symm h''

/-! ## ObservableRelC lifting through mu -/

lemma ObservableRelC_mu_left {R : LocalTypeC → LocalTypeC → Prop} {x : String}
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

lemma ObservableRelC_mu_right {R : LocalTypeC → LocalTypeC → Prop} {x : String}
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

end RumpsteakV2.Coinductive
