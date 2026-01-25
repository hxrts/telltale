import RumpsteakV2.Coinductive.Roundtrip.Part4

set_option linter.dupNamespace false

namespace RumpsteakV2.Coinductive
theorem toCoind_toInductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hprod : ProductiveC t)
    (hback : ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c)
    (hce : EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
             (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t := by
  have hEnvL :
      EnvResolvesL (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_resolvesL_of_backedge (all := Set.Finite.toFinset h)
      (visited := Set.Finite.toFinset h) hback
  have hEnvR : EnvVarR (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) :=
    envOf_varR (Set.Finite.toFinset h) (Set.Finite.toFinset h)
  have hprod_left : ProductiveC (toCoind (toInductive t h)) :=
    productive_toCoind (toInductive t h)
  exact EQ2CE_to_EQ2C' hce hEnvL hEnvR hprod_left hprod

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
  toCoind_toInductive_eq2c_of_env (t := toCoind t) (h := toCoind_regular t)
    (hprod := productive_toCoind t) hEnv

/-- Round-trip in EQ2C for `toCoind` images with explicit back-edge resolution. -/
theorem toCoind_toInductive_eq2c_of_backedge_toCoind (t : LocalTypeR)
    (hback : ∀ c ∈ Set.Finite.toFinset (toCoind_regular t),
      EQ2C (mkVar (nameOf c (Set.Finite.toFinset (toCoind_regular t)))) c) :
    EQ2C (toCoind (toInductive (toCoind t) (toCoind_regular t))) (toCoind t) :=
  toCoind_toInductive_eq2c_of_backedge (t := toCoind t) (h := toCoind_regular t)
    (hprod := productive_toCoind t) hback

/-- Canonical round-trip statement (alias). -/
theorem toCoind_toInductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t :=
  toCoind_toInductive_eq2ce t h

end RumpsteakV2.Coinductive.Roundtrip
