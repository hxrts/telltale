import SessionCoTypes.FullUnfold

/-! # SessionCoTypes.EQ2.HeadInversion

Head inversion for `EQ2` on well-formed types: if `EQ2 a b` and `b` fully
unfolds to a `send` (resp. `recv`), then `a` fully unfolds to a `send`
(resp. `recv`) to the same partner, with branch lists related by
`BranchesRel EQ2` (same labels and payloads, pairwise `EQ2` continuations).
-/

/-
The Problem. A process may carry any `EQ2`-representative of its projected
local type (e.g. a `mu`-folded one). To advance its *own* type we must know
that its head-normal form exposes the same communication as the projection.

Solution Structure. `full_unfold_eq_of_eq2` gives `EQ2` between full unfolds;
well-formedness (closed + contractive) rules out a leading `mu`, so one
`EQ2F` destruct fixes the head constructor. Branch-membership transfer
lemmas for `BranchesRel` follow by induction on `List.Forall₂`.
-/

namespace SessionCoTypes.EQ2.HeadInversion

open SessionTypes.LocalTypeR
open SessionCoTypes.EQ2

/-! ## Head Inversion -/

/-- `EQ2` between full unfolds of well-formed types. -/
theorem eq2_full_unfold_of_wf {a b : LocalTypeR} (hWFa : a.WellFormed)
    (hWFb : b.WellFormed) (h : EQ2 a b) : EQ2 a.fullUnfold b.fullUnfold :=
  SessionCoTypes.FullUnfold.full_unfold_eq_of_eq2 a b hWFa hWFb h

/-- The full unfold of a well-formed type has no leading `mu`. -/
theorem full_unfold_ne_mu {a : LocalTypeR} (hWFa : a.WellFormed) (t : String)
    (body : LocalTypeR) : a.fullUnfold ≠ .mu t body := by
  intro hx
  have hmu := LocalTypeR.full_unfold_non_mu_of_contractive hWFa.contractive hWFa.closed
  rw [hx] at hmu
  simp [LocalTypeR.muHeight] at hmu

/-- Send inversion: if `EQ2 a b` (both well-formed) and `b` fully unfolds to
`send p bs`, then `a` fully unfolds to `send p as` with `BranchesRel EQ2 as bs`. -/
theorem eq2_full_unfold_send_inv {a b : LocalTypeR} {p : String} {bs : List BranchR}
    (hWFa : a.WellFormed) (hWFb : b.WellFormed) (h : EQ2 a b)
    (hb : b.fullUnfold = .send p bs) :
    ∃ as, a.fullUnfold = .send p as ∧ BranchesRel EQ2 as bs := by
  have h1 := eq2_full_unfold_of_wf hWFa hWFb h
  rw [hb] at h1
  have hne := full_unfold_ne_mu hWFa
  cases hx : a.fullUnfold with
  | send q cs =>
      have hf := EQ2.destruct h1
      rw [hx] at hf
      obtain ⟨rfl, hbr⟩ := hf
      exact ⟨cs, rfl, hbr⟩
  | mu t body => exact absurd hx (hne t body)
  | _ => have hf := EQ2.destruct h1; rw [hx] at hf; simp [EQ2F] at hf

/-- Recv inversion: if `EQ2 a b` (both well-formed) and `b` fully unfolds to
`recv p bs`, then `a` fully unfolds to `recv p as` with `BranchesRel EQ2 as bs`. -/
theorem eq2_full_unfold_recv_inv {a b : LocalTypeR} {p : String} {bs : List BranchR}
    (hWFa : a.WellFormed) (hWFb : b.WellFormed) (h : EQ2 a b)
    (hb : b.fullUnfold = .recv p bs) :
    ∃ as, a.fullUnfold = .recv p as ∧ BranchesRel EQ2 as bs := by
  have h1 := eq2_full_unfold_of_wf hWFa hWFb h
  rw [hb] at h1
  have hne := full_unfold_ne_mu hWFa
  cases hx : a.fullUnfold with
  | recv q cs =>
      have hf := EQ2.destruct h1
      rw [hx] at hf
      obtain ⟨rfl, hbr⟩ := hf
      exact ⟨cs, rfl, hbr⟩
  | mu t body => exact absurd hx (hne t body)
  | _ => have hf := EQ2.destruct h1; rw [hx] at hf; simp [EQ2F] at hf

/-! ## Branch Membership Transfer -/

/-- A left branch of a `BranchesRel` has a related right branch with the same label. -/
theorem branches_rel_mem_left {R : Rel} :
    ∀ {as bs : List BranchR}, BranchesRel R as bs → ∀ {x}, x ∈ as →
      ∃ y ∈ bs, x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ R x.2.2 y.2.2
  | [], [], .nil, _, hx => by simp at hx
  | a :: _, b :: _, .cons hab hs, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, List.mem_cons_self, hab.1, hab.2.1, hab.2.2⟩
      · obtain ⟨y, hy, hy'⟩ := branches_rel_mem_left hs hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- A right branch of a `BranchesRel` has a related left branch with the same label. -/
theorem branches_rel_mem_right {R : Rel} :
    ∀ {as bs : List BranchR}, BranchesRel R as bs → ∀ {y}, y ∈ bs →
      ∃ x ∈ as, x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ R x.2.2 y.2.2
  | [], [], .nil, _, hy => by simp at hy
  | a :: _, b :: _, .cons hab hs, y, hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, List.mem_cons_self, hab.1, hab.2.1, hab.2.2⟩
      · obtain ⟨x, hx, hx'⟩ := branches_rel_mem_right hs hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hx'⟩

/-! ## Well-Formed Continuations -/

/-- Continuations of a well-formed type's `send` head-normal form are well-formed. -/
theorem wf_cont_of_full_unfold_send {a : LocalTypeR} {p : String} {bs : List BranchR}
    (hWFa : a.WellFormed) (ha : a.fullUnfold = .send p bs) :
    ∀ lb ∈ bs, lb.2.2.WellFormed := by
  have h := LocalTypeR.WellFormed.full_unfold hWFa
  rw [ha] at h
  exact LocalTypeR.WellFormed.branches_of_send h

/-- Continuations of a well-formed type's `recv` head-normal form are well-formed. -/
theorem wf_cont_of_full_unfold_recv {a : LocalTypeR} {p : String} {bs : List BranchR}
    (hWFa : a.WellFormed) (ha : a.fullUnfold = .recv p bs) :
    ∀ lb ∈ bs, lb.2.2.WellFormed := by
  have h := LocalTypeR.WellFormed.full_unfold hWFa
  rw [ha] at h
  exact LocalTypeR.WellFormed.branches_of_recv h

end SessionCoTypes.EQ2.HeadInversion
