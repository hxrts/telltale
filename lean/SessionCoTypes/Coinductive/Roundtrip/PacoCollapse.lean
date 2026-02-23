
import SessionCoTypes.Coinductive.Roundtrip.Core
import SessionCoTypes.Coinductive.Roundtrip.GpacoCollapse

/- ## Structured Block 1 -/
set_option linter.dupNamespace false

/-! # SessionCoTypes.Coinductive.Roundtrip.PacoCollapse

Mu-aware paco collapse under productivity and sourced erasure versions.
-/

/-
The Problem. The mu-aware paco equality EQ2C_mu_paco allows unfolding on either
side, but we need to show it collapses to standard EQ2C_paco for productive types
(where every mu is eventually unfolded to an observable).

Solution Structure. Proves helper lemmas connecting children and branches via
`mem_children_of_of_mem_branches_of`. Shows paco collapse under productivity: if
types are productive, mu-aware equality equals standard equality. Provides
"sourced" erasure versions tracking the origin of unfolding steps.
-/

namespace SessionCoTypes.Coinductive
-- μ-aware paco collapse (productivity assumption)

lemma head_of_dest {t : LocalTypeC} {h : LocalTypeHead}
    {f : LocalTypeChild h → LocalTypeC}
    (hdest : PFunctor.M.dest t = ⟨h, f⟩) : head t = h := by
  simpa [head] using congrArg Sigma.fst hdest

lemma mk_of_dest {t : LocalTypeC} {h : LocalTypeHead}
    {f : LocalTypeChild h → LocalTypeC}
    (hdest : PFunctor.M.dest t = ⟨h, f⟩) : t = PFunctor.M.mk ⟨h, f⟩ := by
  apply eq_of_dest_eq
  simpa [PFunctor.M.dest_mk] using hdest

lemma list_get_coe_fin_symm {α : Type} (l : List α) (i : Fin l.length) :
    l.get i = l[↑i] := by
  rfl

-- Branch-to-Child Membership Helpers

lemma mem_children_of_of_mem_branches_of {u : LocalTypeC} {b : Label × LocalTypeC}
    (hmem : b ∈ branchesOf u) : b.2 ∈ childrenOf u := by
  cases hdest : PFunctor.M.dest u with
  | mk hhead f =>
      cases hhead with
      | «end» =>
          have : False := by
            simp [branchesOf, hdest] at hmem
          exact this.elim
      | var v =>
          have : False := by
            simp [branchesOf, hdest] at hmem
          exact this.elim
      | mu x =>
          have : False := by
            simp [branchesOf, hdest] at hmem
          exact this.elim
      | send p labels =>
          have hhead' : head u = .send p labels := by
            exact head_of_dest hdest
          have hchildren : childrenOf u = (branchesOf u).map (·.2) :=
            children_of_send_eq_snd_branches_of (t := u) (p := p) (labels := labels) hhead'
          have hmem' : b.2 ∈ (branchesOf u).map (·.2) := by
            exact List.mem_map.mpr ⟨b, hmem, rfl⟩
          rw [hchildren]
          exact hmem'
      | recv p labels =>
          have hhead' : head u = .recv p labels := by
            exact head_of_dest hdest
          have hchildren : childrenOf u = (branchesOf u).map (·.2) :=
            children_of_recv_eq_snd_branches_of (t := u) (p := p) (labels := labels) hhead'
          have hmem' : b.2 ∈ (branchesOf u).map (·.2) := by
            exact List.mem_map.mpr ⟨b, hmem, rfl⟩
          rw [hchildren]
          exact hmem'

-- Reachability from Observable Branches

lemma reachable_of_can_send_c_mem {t : LocalTypeC} {p : String} {bs : List (Label × LocalTypeC)}
/- ## Structured Block 2 -/
    (h : CanSendC t p bs) {b : Label × LocalTypeC} (hmem : b ∈ bs) :
    b.2 ∈ Reachable t := by
  rcases h with ⟨u, labels, hunf, hhead, hbs⟩
  have hreach : u ∈ Reachable t := unfolds_to_c_reachable hunf
  have hmem' : b ∈ branchesOf u := by simpa [hbs] using hmem
  have hchild : childRel u b.2 := child_rel_of_mem_children_of (mem_children_of_of_mem_branches_of hmem')
  exact reachable_step hreach hchild

lemma reachable_of_can_recv_c_mem {t : LocalTypeC} {p : String} {bs : List (Label × LocalTypeC)}
    (h : CanRecvC t p bs) {b : Label × LocalTypeC} (hmem : b ∈ bs) :
    b.2 ∈ Reachable t := by
  rcases h with ⟨u, labels, hunf, hhead, hbs⟩
  have hreach : u ∈ Reachable t := unfolds_to_c_reachable hunf
  have hmem' : b ∈ branchesOf u := by simpa [hbs] using hmem
  have hchild : childRel u b.2 := child_rel_of_mem_children_of (mem_children_of_of_mem_branches_of hmem')
  exact reachable_step hreach hchild

-- Productive μ-paco Collapse

theorem eq2_c_mu_paco_le_paco_of_productive {a b : LocalTypeC}
    (ha : ProductiveC a) (hb : ProductiveC b) (h : EQ2C_mu_paco a b) :
    EQ2C_paco a b := by
  let R : LocalTypeC → LocalTypeC → Prop :=
    fun x y => EQ2C_mu_paco x y ∧ ProductiveC x ∧ ProductiveC y
  have hR : R a b := ⟨h, ha, hb⟩
  refine Paco.paco_coind EQ2CMono R ⊥ ?_ hR
  intro x y hxy
  rcases hxy with ⟨hmu, hx, hy⟩
  have obs_x : ObservableC x := hx x (Relation.ReflTransGen.refl)
  have obs_y : ObservableC y := hy y (Relation.ReflTransGen.refl)
  have hrel : ObservableRelC EQ2C_mu_paco x y := eq2_c_mu_paco_to_obs obs_x obs_y hmu
  refine ⟨obs_x, obs_y, ?_⟩
  cases hrel with
  | is_end ha hb =>
      exact ObservableRelC.is_end ha hb
  | is_var v ha hb =>
      exact ObservableRelC.is_var v ha hb
  -- Productive Collapse: Send Case
  | is_send p bs cs ha_send hb_send hbr =>
      -- Strengthen branch relation with productivity.
      have hbr' : BranchesRelC R bs cs := by
        -- Recurse structurally over the branch lists, tracking membership in the original lists.
        let rec go_send {bs' cs'}
            (hbr : BranchesRelC EQ2C_mu_paco bs' cs')
            (hsub_l : ∀ {b}, b ∈ bs' → b ∈ bs)
            (hsub_r : ∀ {c}, c ∈ cs' → c ∈ cs) : BranchesRelC R bs' cs' := by
          cases hbr with
          | nil => exact List.Forall₂.nil
          | cons hhd htl =>
              rename_i b0 c0 bs'' cs''
              rcases hhd with ⟨hlab, hmu'⟩
              have hreach_l : b0.2 ∈ Reachable x :=
                reachable_of_can_send_c_mem ha_send (hsub_l (by simp))
              have hreach_r : c0.2 ∈ Reachable y :=
                reachable_of_can_send_c_mem hb_send (hsub_r (by simp))
              have hprod_l : ProductiveC b0.2 := productive_of_reachable hx hreach_l
              have hprod_r : ProductiveC c0.2 := productive_of_reachable hy hreach_r
/- ## Structured Block 3 -/
              have hsub_l' : ∀ {b}, b ∈ bs'' → b ∈ bs := by
                intro b hb
                exact hsub_l (by simp [hb])
              have hsub_r' : ∀ {c}, c ∈ cs'' → c ∈ cs := by
                intro c hc
                exact hsub_r (by simp [hc])
              exact List.Forall₂.cons ⟨hlab, ⟨hmu', hprod_l, hprod_r⟩⟩
                (go_send htl hsub_l' hsub_r')
        exact go_send hbr (by intro b hb; exact hb) (by intro c hc; exact hc)
      exact ObservableRelC.is_send p bs cs ha_send hb_send (branches_rel_c_mono (fun _ _ hr => Or.inl hr) hbr')
  -- Productive Collapse: Recv Case
  | is_recv p bs cs ha_recv hb_recv hbr =>
      have hbr' : BranchesRelC R bs cs := by
        let rec go_recv {bs' cs'}
            (hbr : BranchesRelC EQ2C_mu_paco bs' cs')
            (hsub_l : ∀ {b}, b ∈ bs' → b ∈ bs)
            (hsub_r : ∀ {c}, c ∈ cs' → c ∈ cs) : BranchesRelC R bs' cs' := by
          cases hbr with
          | nil => exact List.Forall₂.nil
          | cons hhd htl =>
              rename_i b0 c0 bs'' cs''
              rcases hhd with ⟨hlab, hmu'⟩
              have hreach_l : b0.2 ∈ Reachable x :=
                reachable_of_can_recv_c_mem ha_recv (hsub_l (by simp))
              have hreach_r : c0.2 ∈ Reachable y :=
                reachable_of_can_recv_c_mem hb_recv (hsub_r (by simp))
              have hprod_l : ProductiveC b0.2 := productive_of_reachable hx hreach_l
              have hprod_r : ProductiveC c0.2 := productive_of_reachable hy hreach_r
              have hsub_l' : ∀ {b}, b ∈ bs'' → b ∈ bs := by
                intro b hb
                exact hsub_l (by simp [hb])
              have hsub_r' : ∀ {c}, c ∈ cs'' → c ∈ cs := by
                intro c hc
                exact hsub_r (by simp [hc])
              exact List.Forall₂.cons ⟨hlab, ⟨hmu', hprod_l, hprod_r⟩⟩
                (go_recv htl hsub_l' hsub_r')
        exact go_recv hbr (by intro b hb; exact hb) (by intro c hc; exact hc)
      exact ObservableRelC.is_recv p bs cs ha_recv hb_recv (branches_rel_c_mono (fun _ _ hr => Or.inl hr) hbr')

-- gpaco-based Collapse Criterion

/-- gpaco-based collapse: if μ-paco steps are observable under GpacoRel, then μ-paco collapses. -/
theorem eq2_c_mu_paco_le_paco_of_obs
    (hrr : ∀ a b, EQ2C_mu_paco a b → ObservableRelC GpacoRel a b)
    {a b : LocalTypeC} (h : EQ2C_mu_paco a b) :
    EQ2C_paco a b := by
  -- Delegate to the gpaco collapse lemma in GpacoCollapse.
  exact mu_paco_le_paco_of_obs hrr h

-- Erasure from EQ2CE_resolved'

/-- EQ2CE_resolved' implies EQ2C, assuming productivity on both sides. -/
theorem eq2_ce_resolved'_implies_eq2_c (a b : LocalTypeC) (h : EQ2CE_resolved' a b)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b := by
  have hmu : EQ2C_mu_paco a b := eq2_ce_resolved'_to_mu_paco h
  have hpaco : EQ2C_paco a b := eq2_c_mu_paco_le_paco_of_productive ha hb hmu
  exact paco_to_eq2_c hpaco

-- Erasure from EQ2CE

/-- The main erasure theorem: EQ2CE with resolving env implies EQ2C.
    This uses eq2_ce_resolved'_step_to_eq2_c with the coinductive IH
    eq2_ce_resolved'_implies_eq2_c. -/
theorem eq2_ce_to_eq2_c' {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
/- ## Structured Block 4 -/
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b :=
  eq2_ce_resolved'_implies_eq2_c a b ⟨ρ, hEnvL, hVarR, hce⟩ ha hb

/-- Simplified erasure: EQ2CE with resolving env implies EQ2C.

This uses eq2_ce_to_eq2_c' which builds a bisimulation directly.
-/
theorem eq2_ce_to_eq2_c {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b :=
  -- Delegate to EQ2CE_to_EQ2C' which handles all cases
  eq2_ce_to_eq2_c' hce hEnvL hVarR ha hb

-- Sourced versions (toCoind)

/-- Erasure for toCoind sources, discharging productivity. -/
theorem eq2_ce_to_eq2_c'_to_coind {ρ : EnvPair}
    {a b : SessionTypes.LocalTypeR.LocalTypeR}
    (hce : EQ2CE ρ (toCoind a) (toCoind b))
    (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C (toCoind a) (toCoind b) := by
  -- toCoind images are productive, so discharge hypotheses internally.
  exact eq2_ce_to_eq2_c' hce hEnvL hVarR (productive_to_coind a) (productive_to_coind b)

/-- The key lemma: EQ2CE_resolved implies EQ2C by coinduction.
    This uses eq2_ce_step_to_eq2_c_var_r which handles mu cases via unfolding.
    Delegates to eq2_ce_to_eq2_c'. -/
theorem eq2_ce_resolved_to_eq2_c :
    ∀ ρ a b, EQ2CE_resolved ρ a b → ProductiveC a → ProductiveC b → EQ2C a b := by
  intro ρ a b ⟨hResL, hVarR, hce⟩ ha hb
  exact eq2_ce_to_eq2_c' hce hResL hVarR ha hb

-- Paco-style erasure (alternative)

def EQ2CE_rel_paco (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

theorem eq2_ce_to_eq2_c_paco {a b : LocalTypeC} (hR : EQ2CE_rel_paco a b)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C_paco a b := by
  rcases hR with ⟨ρ, hResL, hVarR, hce⟩
  rw [← eq2_c_eq_paco_bot]
  exact eq2_ce_to_eq2_c' hce hResL hVarR ha hb

-- Sourced versions (toCoind)

/-- Simplified erasure for toCoind sources. -/
theorem eq2_ce_to_eq2_c_to_coind {ρ : EnvPair}
    {a b : SessionTypes.LocalTypeR.LocalTypeR}
    (hce : EQ2CE ρ (toCoind a) (toCoind b))
    (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C (toCoind a) (toCoind b) :=
  eq2_ce_to_eq2_c'_to_coind hce hEnvL hVarR

/-- Resolved erasure for toCoind sources, discharging productivity. -/
theorem eq2_ce_resolved'_implies_eq2_c_to_coind
    {a b : SessionTypes.LocalTypeR.LocalTypeR}
    (h : EQ2CE_resolved' (toCoind a) (toCoind b)) :
    EQ2C (toCoind a) (toCoind b) :=
  eq2_ce_resolved'_implies_eq2_c (toCoind a) (toCoind b) h
    (productive_to_coind a) (productive_to_coind b)

/-- Resolved erasure for toCoind sources (EnvPair version). -/
theorem eq2_ce_resolved_to_eq2_c_to_coind
    {ρ : EnvPair} {a b : SessionTypes.LocalTypeR.LocalTypeR}
    (h : EQ2CE_resolved ρ (toCoind a) (toCoind b)) :
    EQ2C (toCoind a) (toCoind b) :=
  eq2_ce_resolved_to_eq2_c ρ (toCoind a) (toCoind b) h
    (productive_to_coind a) (productive_to_coind b)

/-- Paco-style erasure for toCoind sources, discharging productivity. -/
theorem eq2_ce_to_eq2_c_paco_to_coind
    {a b : SessionTypes.LocalTypeR.LocalTypeR}
    (hR : EQ2CE_rel_paco (toCoind a) (toCoind b)) :
    EQ2C_paco (toCoind a) (toCoind b) :=
  eq2_ce_to_eq2_c_paco hR (productive_to_coind a) (productive_to_coind b)

-- Sourced versions (projTrans)

/-- Erasure for projection sources, discharging productivity. -/
theorem eq2_ce_to_eq2_c_proj_trans {ρ : EnvPair}
/- ## Structured Block 5 -/
    {g₁ g₂ : SessionTypes.GlobalType.GlobalType}
    {role₁ role₂ : String}
    (hce : EQ2CE ρ
      (toCoind (Choreography.Projection.Project.trans g₁ role₁))
      (toCoind (Choreography.Projection.Project.trans g₂ role₂)))
    (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C (toCoind (Choreography.Projection.Project.trans g₁ role₁))
         (toCoind (Choreography.Projection.Project.trans g₂ role₂)) := by
  -- Projection outputs are inductive, so toCoind images are productive.
  have hprod₁ :
      ProductiveC (toCoind (Choreography.Projection.Project.trans g₁ role₁)) :=
    productive_to_coind_of_proj_trans g₁ role₁
  have hprod₂ :
      ProductiveC (toCoind (Choreography.Projection.Project.trans g₂ role₂)) :=
    productive_to_coind_of_proj_trans g₂ role₂
  -- Delegate to the general erasure lemma.
  exact eq2_ce_to_eq2_c' hce hEnvL hVarR hprod₁ hprod₂

/-- Resolved erasure for projTrans sources, discharging productivity. -/
theorem eq2_ce_resolved'_implies_eq2_c_proj_trans
    {g₁ g₂ : SessionTypes.GlobalType.GlobalType}
    {role₁ role₂ : String}
    (h : EQ2CE_resolved'
      (toCoind (Choreography.Projection.Project.trans g₁ role₁))
      (toCoind (Choreography.Projection.Project.trans g₂ role₂))) :
    EQ2C (toCoind (Choreography.Projection.Project.trans g₁ role₁))
         (toCoind (Choreography.Projection.Project.trans g₂ role₂)) := by
  -- Discharge productivity for both projections.
  exact eq2_ce_resolved'_implies_eq2_c _ _ h
    (productive_to_coind_of_proj_trans g₁ role₁)
    (productive_to_coind_of_proj_trans g₂ role₂)

/-- Resolved erasure for projTrans sources (EnvPair version). -/
theorem eq2_ce_resolved_to_eq2_c_proj_trans
    {ρ : EnvPair} {g₁ g₂ : SessionTypes.GlobalType.GlobalType}
    {role₁ role₂ : String}
    (h : EQ2CE_resolved ρ
      (toCoind (Choreography.Projection.Project.trans g₁ role₁))
      (toCoind (Choreography.Projection.Project.trans g₂ role₂))) :
    EQ2C (toCoind (Choreography.Projection.Project.trans g₁ role₁))
         (toCoind (Choreography.Projection.Project.trans g₂ role₂)) := by
  -- Discharge productivity for both projections.
  exact eq2_ce_resolved_to_eq2_c ρ _ _ h
    (productive_to_coind_of_proj_trans g₁ role₁)
    (productive_to_coind_of_proj_trans g₂ role₂)

/-- Paco-style erasure for projTrans sources, discharging productivity. -/
theorem eq2_ce_to_eq2_c_paco_proj_trans
    {g₁ g₂ : SessionTypes.GlobalType.GlobalType}
    {role₁ role₂ : String}
    (hR : EQ2CE_rel_paco
      (toCoind (Choreography.Projection.Project.trans g₁ role₁))
      (toCoind (Choreography.Projection.Project.trans g₂ role₂))) :
    EQ2C_paco (toCoind (Choreography.Projection.Project.trans g₁ role₁))
              (toCoind (Choreography.Projection.Project.trans g₂ role₂)) :=
  eq2_ce_to_eq2_c_paco hR
    (productive_to_coind_of_proj_trans g₁ role₁)
    (productive_to_coind_of_proj_trans g₂ role₂)

end SessionCoTypes.Coinductive
