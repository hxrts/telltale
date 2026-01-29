import RumpsteakV2.Coinductive.Roundtrip.Part4

set_option linter.dupNamespace false

/-! # Roundtrip Part 5

Final round-trip statements and aliases.
-/

namespace RumpsteakV2.Coinductive
open RumpsteakV2.Protocol.LocalTypeR
theorem toCoind_toInductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c)
    (hce : EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
             (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t := by
  -- Use back-edge resolution to construct EnvResolves and discharge productivity on the left.
  have hEnv : EnvResolves (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_resolves_of_backedge (all := Set.Finite.toFinset h)
      (visited := Set.Finite.toFinset h) hback
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_varR (Set.Finite.toFinset h) (Set.Finite.toFinset h)
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_toCoind (toInductive t h)
  exact EQ2CE_to_EQ2C' hce hEnv.1 hEnvR hprod_left hprod

/-- Round-trip in EQ2C assuming back-edge resolution.
    Requires productivity of the RHS. -/
theorem toCoind_toInductive_eq2c_of_backedge (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c) :
    EQ2C (toCoind (toInductive t h)) t :=
  toCoind_toInductive_eq2c_of_eq2ce t h hprod hback (toCoind_toInductive_eq2ce t h)

/-- Round-trip in EQ2C assuming environment resolves back-edges.
    Requires productivity of the RHS. -/
theorem toCoind_toInductive_eq2c_of_env (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hEnv : EnvResolves (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))) :
    EQ2C (toCoind (toInductive t h)) t := by
  -- Discharge productivity on the left using the toCoind image.
  have hce := toCoind_toInductive_eq2ce t h
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_toCoind (toInductive t h)
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_varR (Set.Finite.toFinset h) (Set.Finite.toFinset h)
  exact EQ2CE_to_EQ2C' hce hEnv.1 hEnvR hprod_left hprod

/-- Round-trip in EQ2C for `toCoind` images, discharging productivity. -/
theorem toCoind_toInductive_eq2c_of_env_toCoind (t : LocalTypeR)
    (hEnv : EnvResolves
      (envOf (Set.Finite.toFinset (toCoind_regular t))
        (Set.Finite.toFinset (toCoind_regular t)))) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) :=
by
  -- Use the toCoind erasure lemma to avoid explicit productivity hypotheses.
  have hce := toCoind_toInductive_eq2ce (toCoind t) (toCoind_regular t)
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset (toCoind_regular t))
      (Set.Finite.toFinset (toCoind_regular t))) :=
    envOf_varR (Set.Finite.toFinset (toCoind_regular t))
      (Set.Finite.toFinset (toCoind_regular t))
  exact EQ2CE_to_EQ2C'_toCoind (ρ := envOf (Set.Finite.toFinset (toCoind_regular t))
      (Set.Finite.toFinset (toCoind_regular t))) (a := toInductive (toCoind t) (toCoind_regular t))
      (b := t) hce hEnv.1 hEnvR

/-- Round-trip in EQ2C for `toCoind` images with explicit back-edge resolution. -/
theorem toCoind_toInductive_eq2c_of_backedge_toCoind (t : LocalTypeR)
    (hback : ∀ c ∈ Set.Finite.toFinset (toCoind_regular t),
      EQ2C (mkVar (nameOf c (Set.Finite.toFinset (toCoind_regular t)))) c) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) := by
  -- Convert back-edge resolution to EnvResolves and reuse the toCoind erasure lemma.
  have hEnv : EnvResolves
      (envOf (Set.Finite.toFinset (toCoind_regular t))
        (Set.Finite.toFinset (toCoind_regular t))) :=
    envOf_resolves_of_backedge (all := Set.Finite.toFinset (toCoind_regular t))
      (visited := Set.Finite.toFinset (toCoind_regular t)) hback
  exact toCoind_toInductive_eq2c_of_env_toCoind t hEnv

/-- Canonical round-trip statement (alias). -/
theorem toCoind_toInductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t :=
  toCoind_toInductive_eq2ce t h

end RumpsteakV2.Coinductive
