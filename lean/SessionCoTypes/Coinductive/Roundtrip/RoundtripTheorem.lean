import SessionCoTypes.Coinductive.Roundtrip.RoundtripPostfix

set_option linter.dupNamespace false

namespace SessionCoTypes.Coinductive
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

local instance : DecidableEq LocalTypeC := by
  classical
  infer_instance

theorem toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (h.states.toFinset) (h.states.toFinset))
      (toCoind (toInductive t h)) t := by
  classical
  let all := h.states.toFinset
  let h_closed : IsClosedSet all := reachable_is_closed_set t h
  let R : Rel := fun ρ a b =>
    ∃ (visited : Finset LocalTypeC) (h_visited : visited ⊆ all) (h_current : b ∈ all),
      (a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) ∨
       (b ∉ visited ∧
        a = toCoind (toInductiveBody t all visited b h_closed h_visited h_current))) ∧
      EnvOfSub all ρ
  have hpost : ∀ ρ a b, R ρ a b → EQ2CE_step R ρ a b := by
    simpa [R] using (roundtrip_hpost (t := t) (all := all) (h_closed := h_closed))
  have hR : R (envOf all all) (toCoind (toInductive t h)) t := by
    refine ⟨∅, ?_, ?_, ?_, envOf_sub all all⟩
    · exact Finset.empty_subset _
    · exact List.mem_toFinset.2 h.root_mem
    · exact Or.inl rfl
  exact EQ2CE_coind hpost _ _ _ hR

end SessionCoTypes.Coinductive
