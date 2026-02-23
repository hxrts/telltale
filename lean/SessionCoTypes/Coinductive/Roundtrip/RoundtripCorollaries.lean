import SessionCoTypes.Coinductive.Roundtrip.RoundtripTheorem

set_option linter.dupNamespace false

/-! # SessionCoTypes.Coinductive.Roundtrip.RoundtripCorollaries

Final round-trip statements and aliases.
-/

namespace SessionCoTypes.Coinductive
open SessionTypes.LocalTypeR

/-! ## Core Roundtrip EQ2C Corollaries -/

theorem to_coind_to_inductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ h.states.toFinset, EQ2C (mkVar (nameOf c (h.states.toFinset))) c)
    (hce : EQ2CE (envOf (h.states.toFinset) (h.states.toFinset))
             (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t := by
  -- Use back-edge resolution to construct EnvResolves and discharge productivity on the left.
  have hEnv : EnvResolves (envOf (h.states.toFinset) (h.states.toFinset)) :=
    env_of_resolves_of_backedge (all := h.states.toFinset)
      (visited := h.states.toFinset) hback
  have hEnvR : EnvVarR (envOf (h.states.toFinset) (h.states.toFinset)) :=
    env_of_var_r (h.states.toFinset) (h.states.toFinset)
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_to_coind (toInductive t h)
  exact eq2_ce_to_eq2_c' hce hEnv.1 hEnvR hprod_left hprod

/-- Round-trip in EQ2C assuming back-edge resolution.
    Requires productivity of the RHS. -/
theorem to_coind_to_inductive_eq2c_of_backedge (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ h.states.toFinset, EQ2C (mkVar (nameOf c (h.states.toFinset))) c) :
    EQ2C (toCoind (toInductive t h)) t :=
  to_coind_to_inductive_eq2c_of_eq2ce t h hprod hback (to_coind_to_inductive_eq2ce t h)

/-- Round-trip in EQ2C assuming environment resolves back-edges.
    Requires productivity of the RHS. -/
theorem to_coind_to_inductive_eq2c_of_env (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hEnv : EnvResolves (envOf (h.states.toFinset) (h.states.toFinset))) :
    EQ2C (toCoind (toInductive t h)) t := by
  -- Discharge productivity on the left using the toCoind image.
  have hce := to_coind_to_inductive_eq2ce t h
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_to_coind (toInductive t h)
  have hEnvR : EnvVarR (envOf (h.states.toFinset) (h.states.toFinset)) :=
    env_of_var_r (h.states.toFinset) (h.states.toFinset)
  exact eq2_ce_to_eq2_c' hce hEnv.1 hEnvR hprod_left hprod

/-! ## toCoind-Source Corollaries -/

/-- Round-trip in EQ2C for `toCoind` images, discharging productivity. -/
theorem to_coind_to_inductive_eq2c_of_env_to_coind (t : LocalTypeR)
    (hEnv : EnvResolves
      (envOf (Set.Finite.toFinset (toCoind_regular t))
        (Set.Finite.toFinset (toCoind_regular t)))) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) :=
by
  -- Use the toCoind erasure lemma to avoid explicit productivity hypotheses.
  have hce := to_coind_to_inductive_eq2ce (toCoind t) (toCoind_regular t)
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset (toCoind_regular t))
      (Set.Finite.toFinset (toCoind_regular t))) :=
    env_of_var_r (Set.Finite.toFinset (toCoind_regular t))
      (Set.Finite.toFinset (toCoind_regular t))
  exact eq2_ce_to_eq2_c'_to_coind (ρ := envOf (Set.Finite.toFinset (toCoind_regular t))
      (Set.Finite.toFinset (toCoind_regular t))) (a := toInductive (toCoind t) (toCoind_regular t))
      (b := t) hce hEnv.1 hEnvR

/-! ## toCoind Back-edge Corollary -/

/-- Round-trip in EQ2C for `toCoind` images with explicit back-edge resolution. -/
theorem to_coind_to_inductive_eq2c_of_backedge_to_coind (t : LocalTypeR)
    (hback : ∀ c ∈ Set.Finite.toFinset (toCoind_regular t),
      EQ2C (mkVar (nameOf c (Set.Finite.toFinset (toCoind_regular t)))) c) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) := by
  -- Convert back-edge resolution to EnvResolves and reuse the toCoind erasure lemma.
  have hEnv : EnvResolves
      (envOf (Set.Finite.toFinset (toCoind_regular t))
        (Set.Finite.toFinset (toCoind_regular t))) :=
    env_of_resolves_of_backedge (all := Set.Finite.toFinset (toCoind_regular t))
      (visited := Set.Finite.toFinset (toCoind_regular t)) hback
  exact to_coind_to_inductive_eq2c_of_env_to_coind t hEnv

/-! ## Canonical Alias -/

/-- Canonical round-trip statement (alias). -/
theorem to_coind_to_inductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (h.states.toFinset) (h.states.toFinset))
      (toCoind (toInductive t h)) t :=
  to_coind_to_inductive_eq2ce t h

end SessionCoTypes.Coinductive
