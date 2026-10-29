
import SessionCoTypes.Coinductive.Roundtrip.RoundtripPostfixBodyCase

/-! # Roundtrip Postfix Lemma

Main roundtrip lemma showing coinductive-inductive-coinductive conversion
preserves EQ2 equivalence, using postfix reasoning for recursion. -/

/-
The Problem. The roundtrip `toCoind ∘ toInductive` must preserve EQ2.
The proof uses a parametrized bisimulation with a postfix relation that
tracks visited nodes to handle back-edges in recursive types.

Solution Structure. Define the roundtrip relation R with visited-set
tracking. Prove `roundtrip_hpost` showing R is preserved by EQ2CE steps.
Case split on wrap (aux) vs body forms and back-edge vs fresh visits.
-/

/- ## Structured Block 1 -/
set_option linter.dupNamespace false

namespace SessionCoTypes.Coinductive
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

noncomputable local instance : DecidableEq LocalTypeC := by
  classical
  infer_instance

/-! ## Fresh-Node Unfolding -/

/-- Unfolding `toInductiveAux` at a fresh node: either the canonical body is
wrapped in a `mu` binder named `nameOf b all`, or it is returned unchanged. -/
lemma to_inductive_aux_fresh_cases
    {t : LocalTypeC} {all visited : Finset LocalTypeC} {b : LocalTypeC}
    {h_closed : IsClosedSet all} {h_visited : visited ⊆ all} {h_current : b ∈ all}
    (hmem : b ∉ visited) :
    toInductiveAux t all visited b h_closed h_visited h_current =
        LocalTypeR.mu (nameOf b all) (toInductiveBody t all visited b h_closed h_visited h_current) ∨
      toInductiveAux t all visited b h_closed h_visited h_current =
        toInductiveBody t all visited b h_closed h_visited h_current := by
  have hunf : toInductiveAux t all visited b h_closed h_visited h_current =
      (match head b with
        | .mu _ => LocalTypeR.mu (nameOf b all)
            (toInductiveBody t all visited b h_closed h_visited h_current)
        | .var _ => toInductiveBody t all visited b h_closed h_visited h_current
        | _ => if nameOf b all ∈
              (toInductiveBody t all visited b h_closed h_visited h_current).freeVars then
            LocalTypeR.mu (nameOf b all)
              (toInductiveBody t all visited b h_closed h_visited h_current)
          else toInductiveBody t all visited b h_closed h_visited h_current) := by
    rw [toInductiveAux, dite_eq_right hmem]
    rfl
  rw [hunf]
  split <;> (try split) <;> simp_all

/-! ## Main Roundtrip Lemma -/

/-- Wrap case of `roundtrip_hpost`: `a` is the `toInductiveAux` image of `b`. -/
lemma roundtrip_hpost_wrap_case
    (t : LocalTypeC) (all : Finset LocalTypeC) (h_closed : IsClosedSet all)
    {ρ : EnvPair} {a b : LocalTypeC}
    {visited : Finset LocalTypeC} {h_visited : visited ⊆ all} {h_current : b ∈ all}
    (hsub : EnvOfSub all ρ)
    (hwrap : a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current)) :
    EQ2CE_step (roundtripRel t all h_closed) ρ a b := by
  have hmem_env : b ∈ envL ρ (nameOf b all) := env_of_sub_mem hsub h_current
  by_cases hmem : b ∈ visited
  · have hvar_body : toInductiveAux t all visited b h_closed h_visited h_current =
        LocalTypeR.var (nameOf b all) := by
      unfold toInductiveAux
      simp [hmem, nameOf]
      rfl
    have ha : head a = .var (nameOf b all) := by
      simp [hwrap, hvar_body]
    exact EQ2CE_step.var_left ha hmem_env
  · rcases to_inductive_aux_fresh_cases (h_closed := h_closed) (h_visited := h_visited)
      (h_current := h_current) (t := t) hmem with hmu | hbody
    · have ha : PFunctor.M.dest a = ⟨LocalTypeHead.mu (nameOf b all), fun _ =>
          toCoind (toInductiveBody t all visited b h_closed h_visited h_current)⟩ := by
        simp [hwrap, hmu, to_coind_mu, mkMu, PFunctor.M.dest_mk]
      refine EQ2CE_step.mu_left ha hmem_env ?_
      exact ⟨visited, h_visited, h_current, Or.inr ⟨hmem, rfl⟩,
        env_of_sub_insert_l (nameOf b all) b hsub⟩
    · exact roundtrip_hpost_body_case t all h_closed hsub ⟨hmem, by rw [hwrap, hbody]⟩

/-- Postfix property of the roundtrip relation with respect to `EQ2CE_step`. -/
lemma roundtrip_hpost
    (t : LocalTypeC)
    (all : Finset LocalTypeC)
    (h_closed : IsClosedSet all) :
    let R : Rel := fun ρ a b =>
      ∃ (visited : Finset LocalTypeC) (h_visited : visited ⊆ all) (h_current : b ∈ all),
        (a = toCoind (toInductiveAux t all visited b h_closed h_visited h_current) ∨
         (b ∉ visited ∧
          a = toCoind (toInductiveBody t all visited b h_closed h_visited h_current))) ∧
        EnvOfSub all ρ
    ∀ ρ a b, R ρ a b → EQ2CE_step R ρ a b := by
  intro _ ρ a b hR
  rcases hR with ⟨visited, h_visited, h_current, hcase, hsub⟩
  rcases hcase with hwrap | hcore
  · exact roundtrip_hpost_wrap_case t all h_closed hsub hwrap
  · exact roundtrip_hpost_body_case t all h_closed hsub hcore

end SessionCoTypes.Coinductive
