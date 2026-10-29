import Distributed.Families.FLP.Valency

set_option autoImplicit false

/-! # Distributed.Families.FLP.Bivalence

FLP Lemma 3 (Fischer–Lynch–Paterson 1985): if `C` is an accessible bivalent
configuration and `e` is applicable to `C`, then some configuration reached
from `C` by a schedule ending in `e` (and not applying `e` earlier) is bivalent.

Proof. Let `𝒞` be the configurations reached from `C` without applying `e` and
`𝒟 = e(𝒞)`. Assume no member of `𝒟` is bivalent. Write `b X` for "`e(X)` can
decide `true`".
1. Both valencies occur in `𝒟` (`exists_flip_from`), so walking along a
   schedule inside `𝒞` yields neighbours `C₀`, `C₁ = e'(C₀)` with
   `b C₀ ≠ b C₁` (`walk`).
2. If `e'` and `e` are steps of different processes they commute, so
   `e(C₁) = e'(e(C₀))` is reachable from `e(C₀)`: contradiction
   (`neighbours_distinct`).
3. If they are steps of the same process `p`, take a `p`-free deciding
   schedule `σ` from `C₀` (termination with `p` crashed); by commutativity both
   `e(C₀)` and `e(C₁)` reach extensions of `σ(C₀)`, so they share its decision:
   contradiction (`neighbours_same`).
-/

namespace Distributed
namespace FLP
namespace Async

variable {Proc Msg St : Type} [DecidableEq Proc] [DecidableEq Msg]
variable {P : Protocol Proc Msg St}

/-! ## Schedule Splitting and Valency Facts -/

/-- Split a schedule at the first occurrence of `e`. -/
theorem first_split {e : Event Proc Msg} : ∀ {σ : Schedule Proc Msg}, e ∈ σ →
    ∃ α β, σ = α ++ e :: β ∧ e ∉ α
  | [], h => by cases h
  | a :: σ, h => by
    by_cases hae : a = e
    · exact ⟨[], σ, by rw [hae]; rfl, fun h => (List.not_mem_nil h).elim⟩
    · have hm : e ∈ σ := (List.mem_cons.1 h).resolve_left (Ne.symm hae)
      obtain ⟨α, β, rfl, hα⟩ := first_split hm
      refine ⟨a :: α, β, rfl, ?_⟩
      simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm hae, hα⟩

/-- A decision reachable from `C` is reachable from `e(X)` for some `X` reached
from `C` without applying `e`. -/
theorem reach_via {C : Config Proc Msg St} {e : Event Proc Msg} {w : Bool}
    (he : Applicable C e) (h : CanDecide P C w) :
    ∃ α, e ∉ α ∧ Appl P C α ∧ CanDecide P (apply P (exec P C α) e) w := by
  obtain ⟨σ, hσ, hd⟩ := h
  by_cases hm : e ∈ σ
  · obtain ⟨α, β, rfl, hα⟩ := first_split hm
    rw [appl_append] at hσ
    exact ⟨α, hα, hσ.1, β, hσ.2.2, by simpa [exec] using hd⟩
  · exact ⟨σ, hm, hσ, [], trivial, decided_apply P e hd⟩

/-- For a non-bivalent `D`, any reachable decision `w` determines whether `D`
can decide `true`. -/
theorem valence_of_reach {D : Config Proc Msg St} {τ : Schedule Proc Msg} {w : Bool}
    (hD : ¬ Bivalent P D) (hτ : Appl P D τ) (hd : Decided P (exec P D τ) w) :
    CanDecide P D true ↔ w = true := by
  have hw : CanDecide P D w := ⟨τ, hτ, hd⟩
  cases w with
  | true => exact ⟨fun _ => rfl, fun _ => hw⟩
  | false => exact ⟨fun ht => absurd ⟨ht, hw⟩ hD, fun h => by cases h⟩

/-- Walking along a schedule on which a predicate flips finds an adjacent flip. -/
theorem walk (e : Event Proc Msg) (b : Config Proc Msg St → Prop) :
    ∀ (α : Schedule Proc Msg) (X : Config Proc Msg St), e ∉ α → Appl P X α →
      ¬ (b X ↔ b (exec P X α)) →
      ∃ β e', e ∉ β ∧ e' ≠ e ∧ Appl P X (β ++ [e']) ∧
        ¬ (b (exec P X β) ↔ b (apply P (exec P X β) e')) := by
  intro α
  induction α with
  | nil => intro X _ _ h; exact absurd Iff.rfl h
  | cons a α ih =>
    intro X hα ha hne
    simp only [List.mem_cons, not_or] at hα
    by_cases hab : (b X ↔ b (apply P X a))
    · obtain ⟨β, e', hβ, he', hap, hflip⟩ :=
        ih (apply P X a) hα.2 ha.2 (fun h => hne (hab.trans h))
      refine ⟨a :: β, e', ?_, he', ⟨ha.1, hap⟩, hflip⟩
      simp only [List.mem_cons, not_or]
      exact ⟨hα.1, hβ⟩
    · exact ⟨[], a, fun h => (List.not_mem_nil h).elim, Ne.symm hα.1, ⟨ha.1, trivial⟩, hab⟩

/-! ## The Neighbour Contradiction -/

section Lemma3

variable [Finite Proc] [Countable Msg]
variable {C : Config Proc Msg St} {e : Event Proc Msg}

/-- No configuration `e(X)`, `X ∈ 𝒞`, is bivalent (the hypothesis refuted). -/
def NoBivalentAfter (P : Protocol Proc Msg St) (C : Config Proc Msg St)
    (e : Event Proc Msg) : Prop :=
  ∀ α, e ∉ α → Appl P C α → ¬ Bivalent P (apply P (exec P C α) e)

/-- Both valencies occur in `𝒟`: some `X ∈ 𝒞` has `b X ≠ b C`. -/
theorem exists_flip_from (Hno : NoBivalentAfter P C e) (hB : Bivalent P C)
    (he : Applicable C e) : ∃ α, e ∉ α ∧ Appl P C α ∧
      ¬ (CanDecide P (apply P C e) true ↔ CanDecide P (apply P (exec P C α) e) true) := by
  by_cases hbC : CanDecide P (apply P C e) true
  · obtain ⟨α, hα, ha, τ, hτ, hd⟩ := reach_via he hB.2
    have hK := valence_of_reach (Hno α hα ha) hτ hd
    exact ⟨α, hα, ha, fun h => absurd (hK.1 (h.1 hbC)) (by decide)⟩
  · obtain ⟨α, hα, ha, hw⟩ := reach_via he hB.1
    exact ⟨α, hα, ha, fun h => hbC (h.2 hw)⟩

/-- Neighbours by a step of a different process cannot flip `b`. -/
theorem neighbours_distinct (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    {C₀ : Config Proc Msg St} {e' : Event Proc Msg} (hacc : Accessible P C₀)
    (hD0 : ¬ Bivalent P (apply P C₀ e)) (hD1 : ¬ Bivalent P (apply P (apply P C₀ e') e))
    (he : Applicable C₀ e) (he' : Applicable C₀ e') (hp : e.1 ≠ e'.1) :
    (CanDecide P (apply P C₀ e) true ↔ CanDecide P (apply P (apply P C₀ e') e) true) := by
  have hne : e ≠ e' := fun h => hp (by rw [h])
  have hcomm := apply_comm P C₀ hp he he'
  have ha1 : Applicable (apply P C₀ e) e' := applicable_apply_of_ne P he' hne
  have hacc1 : Accessible P (apply P (apply P C₀ e') e) := by
    rw [← hcomm]
    exact accessible_exec P (accessible_exec P hacc (σ := [e]) ⟨he, trivial⟩)
      (σ := [e']) ⟨ha1, trivial⟩
  obtain ⟨r, hr⟩ := partner h2 e.1
  obtain ⟨σ, -, hσ, w, hd⟩ := crash_decides hT hacc1 hr
  rw [valence_of_reach hD1 hσ hd]
  refine valence_of_reach hD0 (τ := e' :: σ) ⟨ha1, ?_⟩ ?_
  · rw [hcomm]; exact hσ
  · show Decided P (exec P (apply P (apply P C₀ e) e') σ) w
    rw [hcomm]; exact hd

/-- Neighbours by a step of the same process cannot flip `b`. -/
theorem neighbours_same (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    {C₀ : Config Proc Msg St} {e' : Event Proc Msg} (hacc : Accessible P C₀)
    (hD0 : ¬ Bivalent P (apply P C₀ e)) (hD1 : ¬ Bivalent P (apply P (apply P C₀ e') e))
    (he : Applicable C₀ e) (he' : Applicable C₀ e') (hne : e' ≠ e) (hp : e.1 = e'.1) :
    (CanDecide P (apply P C₀ e) true ↔ CanDecide P (apply P (apply P C₀ e') e) true) := by
  obtain ⟨r, hr⟩ := partner h2 e.1
  obtain ⟨σ, hfree, hσ, w, hd⟩ := crash_decides hT hacc hr
  obtain ⟨h1, h2', -⟩ := commute_pfree P hfree he hσ
  obtain ⟨h1', h2'', -⟩ := commute_pfree P (hp ▸ hfree) he' hσ
  obtain ⟨h1'', h2''', -⟩ := commute_pfree P hfree (applicable_apply_of_ne P he hne) h1'
  rw [valence_of_reach hD0 h1 (by rw [h2']; exact decided_apply P e hd),
    valence_of_reach hD1 h1'' (by
      rw [h2''', h2'']; exact decided_apply P e (decided_apply P e' hd))]

/-- FLP Lemma 3: bivalence can be preserved while applying any applicable event. -/
theorem bivalent_extension (hT : Termination P) (h2 : ∃ p q : Proc, p ≠ q)
    (hC : Accessible P C) (hB : Bivalent P C) (he : Applicable C e) :
    ∃ σ, Appl P C (σ ++ [e]) ∧ Bivalent P (exec P C (σ ++ [e])) := by
  by_contra hno
  have Hno : NoBivalentAfter P C e := fun α hα ha hbiv => hno ⟨α,
    (appl_append P _ _ _).2 ⟨ha, (appl_singleton P _ _).2 (applicable_exec_of_not_mem P he hα)⟩,
    by simpa [exec] using hbiv⟩
  obtain ⟨α, hα, ha, hflip⟩ := exists_flip_from Hno hB he
  obtain ⟨β, e', hβ, he', hap, hflip'⟩ :=
    walk e (fun X => CanDecide P (apply P X e) true) α C hα ha (by simpa [exec] using hflip)
  rw [appl_append, appl_singleton] at hap
  have hβe : e ∉ β ++ [e'] := by simp [hβ, Ne.symm he']
  have hD1 := Hno _ hβe ((appl_append P _ _ _).2 ⟨hap.1, (appl_singleton P _ _).2 hap.2⟩)
  simp only [exec_append, exec] at hD1
  have hacc := accessible_exec P hC hap.1
  have hapE := applicable_exec_of_not_mem P he hβ
  by_cases hp : e.1 = e'.1
  · exact hflip' (neighbours_same hT h2 hacc (Hno β hβ hap.1) hD1 hapE hap.2 he' hp)
  · exact hflip' (neighbours_distinct hT h2 hacc (Hno β hβ hap.1) hD1 hapE hap.2 hp)

end Lemma3

end Async
end FLP
end Distributed
