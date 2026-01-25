import RumpsteakV2.Coinductive.Roundtrip.Part1

set_option linter.dupNamespace false

namespace RumpsteakV2.Coinductive
/-! ## μ-aware paco collapse (productivity assumption) -/

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

lemma mem_childrenOf_of_mem_branchesOf {u : LocalTypeC} {b : Label × LocalTypeC}
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
            childrenOf_send_eq_snd_branchesOf (t := u) (p := p) (labels := labels) hhead'
          have hmem' : b.2 ∈ (branchesOf u).map (·.2) := by
            exact List.mem_map.mpr ⟨b, hmem, rfl⟩
          rw [hchildren]
          exact hmem'
      | recv p labels =>
          have hhead' : head u = .recv p labels := by
            exact head_of_dest hdest
          have hchildren : childrenOf u = (branchesOf u).map (·.2) :=
            childrenOf_recv_eq_snd_branchesOf (t := u) (p := p) (labels := labels) hhead'
          have hmem' : b.2 ∈ (branchesOf u).map (·.2) := by
            exact List.mem_map.mpr ⟨b, hmem, rfl⟩
          rw [hchildren]
          exact hmem'

lemma reachable_of_canSendC_mem {t : LocalTypeC} {p : String} {bs : List (Label × LocalTypeC)}
    (h : CanSendC t p bs) {b : Label × LocalTypeC} (hmem : b ∈ bs) :
    b.2 ∈ Reachable t := by
  rcases h with ⟨u, labels, hunf, hhead, hbs⟩
  have hreach : u ∈ Reachable t := UnfoldsToC_reachable hunf
  have hmem' : b ∈ branchesOf u := by simpa [hbs] using hmem
  have hchild : childRel u b.2 := childRel_of_mem_childrenOf (mem_childrenOf_of_mem_branchesOf hmem')
  exact reachable_step hreach hchild

lemma reachable_of_canRecvC_mem {t : LocalTypeC} {p : String} {bs : List (Label × LocalTypeC)}
    (h : CanRecvC t p bs) {b : Label × LocalTypeC} (hmem : b ∈ bs) :
    b.2 ∈ Reachable t := by
  rcases h with ⟨u, labels, hunf, hhead, hbs⟩
  have hreach : u ∈ Reachable t := UnfoldsToC_reachable hunf
  have hmem' : b ∈ branchesOf u := by simpa [hbs] using hmem
  have hchild : childRel u b.2 := childRel_of_mem_childrenOf (mem_childrenOf_of_mem_branchesOf hmem')
  exact reachable_step hreach hchild

theorem EQ2C_mu_paco_le_paco_of_productive {a b : LocalTypeC}
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
  have hrel : ObservableRelC EQ2C_mu_paco x y := EQ2C_mu_paco_to_obs obs_x obs_y hmu
  refine ⟨obs_x, obs_y, ?_⟩
  cases hrel with
  | is_end ha hb =>
      exact ObservableRelC.is_end ha hb
  | is_var v ha hb =>
      exact ObservableRelC.is_var v ha hb
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
                reachable_of_canSendC_mem ha_send (hsub_l (by simp))
              have hreach_r : c0.2 ∈ Reachable y :=
                reachable_of_canSendC_mem hb_send (hsub_r (by simp))
              have hprod_l : ProductiveC b0.2 := productive_of_reachable hx hreach_l
              have hprod_r : ProductiveC c0.2 := productive_of_reachable hy hreach_r
              have hsub_l' : ∀ {b}, b ∈ bs'' → b ∈ bs := by
                intro b hb
                exact hsub_l (by simp [hb])
              have hsub_r' : ∀ {c}, c ∈ cs'' → c ∈ cs := by
                intro c hc
                exact hsub_r (by simp [hc])
              exact List.Forall₂.cons ⟨hlab, ⟨hmu', hprod_l, hprod_r⟩⟩
                (go_send htl hsub_l' hsub_r')
        exact go_send hbr (by intro b hb; exact hb) (by intro c hc; exact hc)
      exact ObservableRelC.is_send p bs cs ha_send hb_send (BranchesRelC_mono (fun _ _ hr => Or.inl hr) hbr')
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
                reachable_of_canRecvC_mem ha_recv (hsub_l (by simp))
              have hreach_r : c0.2 ∈ Reachable y :=
                reachable_of_canRecvC_mem hb_recv (hsub_r (by simp))
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
      exact ObservableRelC.is_recv p bs cs ha_recv hb_recv (BranchesRelC_mono (fun _ _ hr => Or.inl hr) hbr')

/-- EQ2CE_resolved' implies EQ2C, assuming productivity on both sides. -/
theorem EQ2CE_resolved'_implies_EQ2C (a b : LocalTypeC) (h : EQ2CE_resolved' a b)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b := by
  have hmu : EQ2C_mu_paco a b := EQ2CE_resolved'_to_mu_paco h
  have hpaco : EQ2C_paco a b := EQ2C_mu_paco_le_paco_of_productive ha hb hmu
  exact paco_to_EQ2C hpaco

/-- The main erasure theorem: EQ2CE with resolving env implies EQ2C.
    This uses EQ2CE_resolved'_step_to_EQ2C with the coinductive IH
    EQ2CE_resolved'_implies_EQ2C. -/
theorem EQ2CE_to_EQ2C' {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b :=
  EQ2CE_resolved'_implies_EQ2C a b ⟨ρ, hEnvL, hVarR, hce⟩ ha hb

/-- Simplified erasure: EQ2CE with resolving env implies EQ2C.

This uses EQ2CE_to_EQ2C' which builds a bisimulation directly.
-/
theorem EQ2CE_to_EQ2C {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C a b :=
  -- Delegate to EQ2CE_to_EQ2C' which handles all cases
  EQ2CE_to_EQ2C' hce hEnvL hVarR ha hb

/-- The key lemma: EQ2CE_resolved implies EQ2C by coinduction.
    This uses EQ2CE_step_to_EQ2C_varR which handles mu cases via unfolding.
    Delegates to EQ2CE_to_EQ2C'. -/
theorem EQ2CE_resolved_to_EQ2C :
    ∀ ρ a b, EQ2CE_resolved ρ a b → ProductiveC a → ProductiveC b → EQ2C a b := by
  intro ρ a b ⟨hResL, hVarR, hce⟩ ha hb
  exact EQ2CE_to_EQ2C' hce hResL hVarR ha hb

/-! ## Paco-style erasure (alternative) -/

def EQ2CE_rel_paco (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

theorem EQ2CE_to_EQ2C_paco {a b : LocalTypeC} (hR : EQ2CE_rel_paco a b)
    (ha : ProductiveC a) (hb : ProductiveC b) :
    EQ2C_paco a b := by
  rcases hR with ⟨ρ, hResL, hVarR, hce⟩
  rw [← EQ2C_eq_paco_bot]
  exact EQ2CE_to_EQ2C' hce hResL hVarR ha hb

end RumpsteakV2.Coinductive.Roundtrip
