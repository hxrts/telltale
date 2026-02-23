
import Mathlib
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.Bridge
import SessionCoTypes.Coinductive.Observable
import SessionCoTypes.Coinductive.RegularityLemmas
import SessionCoTypes.Coinductive.ToInductive
import SessionCoTypes.Coinductive.ToCoindInjectivity
import SessionCoTypes.Coinductive.WellFormed
import SessionTypes.LocalTypeR
import Choreography.Projection.Project

/- ## Structured Block 1 -/
set_option linter.dupNamespace false

/-! # Round-Trip Helpers

Structural lemmas for toCoind supporting round-trip correctness proofs. -/

/-
The Problem. Round-trip correctness requires structural lemmas about toCoind:
children of toCoind images are themselves toCoind images, size bounds for
recursive descent termination, visited set invariants for cycle detection.

Solution Structure. Proves child_rel_to_coind for children of toCoind images,
size bounds for branches in send/recv, child_rel_to_coind_size combining bounds,
VisitedLt for visited set invariant, and free variable hygiene lemmas.
-/

namespace SessionCoTypes.Coinductive

open Classical
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR

-- Children of `toCoind` are themselves `toCoind`

lemma child_rel_to_coind {t : LocalTypeR} {c : LocalTypeC}
    (h : childRel (toCoind t) c) : ∃ u : LocalTypeR, c = toCoind u := by
  cases t with
  | «end» =>
      rcases child_rel_to_children h with ⟨i, _⟩
      cases i
  | var x =>
      rcases child_rel_to_children h with ⟨i, _⟩
      cases i
  | mu x body =>
      rcases child_rel_to_children h with ⟨i, hi⟩
      cases i
      refine ⟨body, ?_⟩
      -- The unique child of a mu node is its body.
      simpa [toCoind, children, mkMu] using hi.symm
  | send p bs =>
      rcases child_rel_to_children h with ⟨i, hi⟩
      have hi' : children (mkSend p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mk_send] using hi'
      let i' : Fin bs.length :=
        castFin (to_coind_branches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2.2, ?_⟩
      have hcont :
          ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i')).2 =
            toCoind (bs.get i').2.2 := by
        simpa using to_coind_branches_get_snd (bs := bs) i'
      have hidx :
          castFin (by simp) i =
            castFin (to_coind_branches_length bs).symm i' := by
        cases i
        simp [i', castFin]
      simpa [hchild, hidx] using hcont
  -- child_rel_to_coind: recv case
  | recv p bs =>
      rcases child_rel_to_children h with ⟨i, hi⟩
      have hi' : children (mkRecv p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mk_recv] using hi'
      let i' : Fin bs.length :=
        castFin (to_coind_branches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2.2, ?_⟩
      have hcont :
/- ## Structured Block 2 -/
          ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i')).2 =
            toCoind (bs.get i').2.2 := by
        simpa using to_coind_branches_get_snd (bs := bs) i'
      have hidx :
          castFin (by simp) i =
            castFin (to_coind_branches_length bs).symm i' := by
        cases i
        simp [i', castFin]
      simpa [hchild, hidx] using hcont

-- Reachability of `toCoind` subterms

lemma reachable_to_coind {t : LocalTypeR} {c : LocalTypeC}
    (h : c ∈ Reachable (toCoind t)) : ∃ u : LocalTypeR, c = toCoind u := by
  induction h with
  | refl =>
      exact ⟨t, rfl⟩
  | tail hprev hstep ih =>
      rename_i b c
      rcases ih with ⟨u, hu⟩
      have hstep' : childRel (toCoind u) c := by
        simpa [hu] using hstep
      rcases child_rel_to_coind hstep' with ⟨u', hu'⟩
      exact ⟨u', hu'⟩

lemma productive_to_coind (t : LocalTypeR) : ProductiveC (toCoind t) := by
  intro c hc
  rcases reachable_to_coind (t := t) hc with ⟨u, rfl⟩
  exact observable_to_coind u

/-- Projection via `trans` yields a productive `toCoind` image. -/
lemma productive_to_coind_of_proj_trans (g : GlobalType) (role : String) :
    ProductiveC (toCoind (Choreography.Projection.Project.trans g role)) := by
  -- Reduce to the generic toCoind productivity lemma.
  exact productive_to_coind (Choreography.Projection.Project.trans g role)

-- Size bounds for branch elements

@[simp] lemma size_of_get_lt_size_of_branches {bs : List BranchR} (i : Fin bs.length) :
    sizeOf (bs.get i).2.2 < sizeOf bs := by
  induction bs with
  | nil =>
      exact (Fin.elim0 i)
  | cons head tail ih =>
      cases i using Fin.cases with
      | zero =>
          cases head with
          | mk label rest =>
            cases rest with
            | mk vt cont =>
              simpa using (size_of_cont_lt_size_of_branches label vt cont tail)
      | succ i =>
          have hlt := ih i
          have htail : sizeOf tail < sizeOf (head :: tail) :=
            size_of_tail_lt_size_of_branches head tail
          exact lt_trans hlt htail

@[simp] lemma size_of_get_lt_size_of_send {p : String} {bs : List BranchR}
    (i : Fin bs.length) :
    sizeOf (bs.get i).2.2 < sizeOf (LocalTypeR.send p bs) := by
  exact lt_trans (size_of_get_lt_size_of_branches i) (size_of_branches_lt_size_of_send p bs)

/- ## Structured Block 3 -/
@[simp] lemma size_of_get_lt_size_of_recv {p : String} {bs : List BranchR}
    (i : Fin bs.length) :
    sizeOf (bs.get i).2.2 < sizeOf (LocalTypeR.recv p bs) := by
  exact lt_trans (size_of_get_lt_size_of_branches i) (size_of_branches_lt_size_of_recv p bs)

@[simp] lemma size_of_get_lt_of_send_eq {t : LocalTypeR} {p : String}
    {bs : List BranchR} (i : Fin bs.length)
    (h : t = LocalTypeR.send p bs) :
    sizeOf (bs.get i).2.2 < sizeOf t := by
  subst h
  simpa using (size_of_get_lt_size_of_send (p := p) (bs := bs) i)

@[simp] lemma size_of_get_lt_of_recv_eq {t : LocalTypeR} {p : String}
    {bs : List BranchR} (i : Fin bs.length)
    (h : t = LocalTypeR.recv p bs) :
    sizeOf (bs.get i).2.2 < sizeOf t := by
  subst h
  simpa using (size_of_get_lt_size_of_recv (p := p) (bs := bs) i)

-- childRel with size bound

lemma child_rel_to_coind_size {t : LocalTypeR} {c : LocalTypeC}
    (h : childRel (toCoind t) c) :
    ∃ u : LocalTypeR, c = toCoind u ∧ sizeOf u < sizeOf t := by
  cases t with
  | «end» =>
      rcases child_rel_to_children h with ⟨i, _⟩
      cases i
  | var x =>
      rcases child_rel_to_children h with ⟨i, _⟩
      cases i
  | mu x body =>
      rcases child_rel_to_children h with ⟨i, hi⟩
      cases i
      refine ⟨body, ?_, ?_⟩
      · simpa [toCoind, children, mkMu] using hi.symm
      · exact size_of_body_lt_size_of_mu x body
  | send p bs =>
      rcases child_rel_to_children h with ⟨i, hi⟩
      have hi' : children (mkSend p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mk_send] using hi'
      let i' : Fin bs.length :=
        castFin (to_coind_branches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2.2, ?_, ?_⟩
      · have hcont :
            ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i')).2 =
              toCoind (bs.get i').2.2 := by
          simpa using to_coind_branches_get_snd (bs := bs) i'
        have hidx :
            castFin (by simp) i =
              castFin (to_coind_branches_length bs).symm i' := by
          cases i
/- ## Structured Block 4 -/
          rfl
        simpa [hchild, hidx] using hcont
      · have hlt : sizeOf (bs.get i').2.2 < sizeOf bs := size_of_get_lt_size_of_branches i'
        exact lt_trans hlt (size_of_branches_lt_size_of_send p bs)
  -- child_rel_to_coind_size: recv case
  | recv p bs =>
      rcases child_rel_to_children h with ⟨i, hi⟩
      have hi' : children (mkRecv p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mk_recv] using hi'
      let i' : Fin bs.length :=
        castFin (to_coind_branches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2.2, ?_, ?_⟩
      · have hcont :
            ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i')).2 =
              toCoind (bs.get i').2.2 := by
          simpa using to_coind_branches_get_snd (bs := bs) i'
        have hidx :
            castFin (by simp) i =
              castFin (to_coind_branches_length bs).symm i' := by
          cases i
          rfl
        simpa [hchild, hidx] using hcont
      · have hlt : sizeOf (bs.get i').2.2 < sizeOf bs := size_of_get_lt_size_of_branches i'
        exact lt_trans hlt (size_of_branches_lt_size_of_recv p bs)

-- VisitedLt invariants

/-- Visited nodes correspond to strictly larger inductive terms. -/
def VisitedLt (t : LocalTypeR) (visited : Finset LocalTypeC) : Prop :=
  ∀ c ∈ visited, ∃ u : LocalTypeR, c = toCoind u ∧ sizeOf t < sizeOf u

lemma visited_lt_not_mem {t : LocalTypeR} {visited : Finset LocalTypeC}
    (hvis : VisitedLt t visited) : toCoind t ∉ visited := by
  intro hmem
  rcases hvis _ hmem with ⟨u, hu, hlt⟩
  have : t = u := to_coind_injective hu
  subst this
  exact lt_irrefl _ hlt

lemma visited_lt_insert {t u : LocalTypeR} {visited : Finset LocalTypeC}
    (hsize : sizeOf u < sizeOf t) (hvis : VisitedLt t visited) :
    VisitedLt u (insert (toCoind t) visited) := by
  intro c hc
  have hc' := Finset.mem_insert.mp hc
  cases hc' with
  | inl hct =>
      exact ⟨t, hct, hsize⟩
  | inr hc =>
      rcases hvis _ hc with ⟨u', hu', hlt⟩
      exact ⟨u', hu', lt_trans hsize hlt⟩

-- childRel lemmas for specific constructors

lemma child_rel_to_coind_mu {x : String} {body : LocalTypeR} :
    childRel (toCoind (.mu x body)) (toCoind body) := by
  refine ⟨.mu x, (fun _ => toCoind body), (), ?_, rfl⟩
  rfl

/- ## Structured Block 5 -/
lemma child_rel_to_coind_send {p : String} {bs : List BranchR} (i : Fin bs.length) :
    childRel (toCoind (.send p bs)) (toCoind (bs.get i).2.2) := by
  refine ⟨head (toCoind (.send p bs)), children (toCoind (.send p bs)), ?_, rfl, ?_⟩
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [to_coind_branches_length]
    exact castFin hlen.symm i
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [to_coind_branches_length]
    have hchild' := children_mk_send p (toCoindBranches bs) (castFin hlen.symm i)
    have hcont :
        ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i)).2 =
          toCoind (bs.get i).2.2 := by
      simpa using to_coind_branches_get_snd (bs := bs) i
    have hidx :
        castFin (by simp) (castFin hlen.symm i) =
          castFin (to_coind_branches_length bs).symm i := by
      ext
      rfl
    have hchild :
        children (toCoind (.send p bs)) (castFin hlen.symm i) =
          ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i)).2 := by
      simpa [toCoind, hidx, -children_mk_send] using hchild'
    exact hchild.trans hcont

-- childRel lemmas for specific constructors: recv case

lemma child_rel_to_coind_recv {p : String} {bs : List BranchR} (i : Fin bs.length) :
    childRel (toCoind (.recv p bs)) (toCoind (bs.get i).2.2) := by
  refine ⟨head (toCoind (.recv p bs)), children (toCoind (.recv p bs)), ?_, rfl, ?_⟩
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [to_coind_branches_length]
    exact castFin hlen.symm i
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [to_coind_branches_length]
    have hchild' := children_mk_recv p (toCoindBranches bs) (castFin hlen.symm i)
    have hcont :
        ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i)).2 =
          toCoind (bs.get i).2.2 := by
      simpa using to_coind_branches_get_snd (bs := bs) i
    have hidx :
        castFin (by simp) (castFin hlen.symm i) =
          castFin (to_coind_branches_length bs).symm i := by
      ext
      rfl
    have hchild :
        children (toCoind (.recv p bs)) (castFin hlen.symm i) =
          ((toCoindBranches bs).get (castFin (to_coind_branches_length bs).symm i)).2 := by
      simpa [toCoind, hidx, -children_mk_recv] using hchild'
    exact hchild.trans hcont

-- Free variable lemmas

/- ## Structured Block 6 -/
lemma mem_free_vars_of_branches {bs : List BranchR} {v : String} :
    v ∈ SessionTypes.LocalTypeR.freeVarsOfBranches bs → ∃ b ∈ bs, v ∈ b.2.2.freeVars := by
  induction bs with
  | nil =>
      intro hv
      cases hv
  | cons b bs ih =>
      intro hv
      simp [SessionTypes.LocalTypeR.freeVarsOfBranches] at hv
      cases hv with
      | inl h =>
          exact ⟨b, by simp, h⟩
      | inr h =>
          rcases ih h with ⟨b', hb', hv'⟩
          exact ⟨b', by simp [hb'], hv'⟩

-- Free variable lemmas: namesIn inclusion

lemma free_vars_subset_names_in {t : LocalTypeR} {all : Finset LocalTypeC}
    (h_closed : IsClosedSet all) (hmem : toCoind t ∈ all) :
    ∀ v, v ∈ t.freeVars → v ∈ namesIn all := by
  classical
  cases t with
  | «end» =>
      intro v hv
      simp [LocalTypeR.freeVars] at hv
  | var x =>
      intro w hw
      have hw' : w = x := by
        simpa [LocalTypeR.freeVars] using hw
      have hmem' : mkVar w ∈ all := by
        simpa [toCoind, hw'] using hmem
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨mkVar w, hmem', by simp [namesOf]⟩
  | mu x body =>
      intro v hv
      have hchild : childRel (toCoind (.mu x body)) (toCoind body) :=
        child_rel_to_coind_mu (x := x) (body := body)
      have hbody_mem : toCoind body ∈ all := mem_of_closed_child h_closed hmem hchild
      have hv' : v ∈ body.freeVars := by
        have hv'' : v ∈ body.freeVars ∧ v ≠ x := by
          simpa [LocalTypeR.freeVars] using hv
        exact hv''.1
      exact free_vars_subset_names_in (t := body) (all := all) h_closed hbody_mem v hv'
  | send p bs =>
      intro v hv
      have hv' : v ∈ SessionTypes.LocalTypeR.freeVarsOfBranches bs := by
        simpa [LocalTypeR.freeVars] using hv
      rcases mem_free_vars_of_branches (bs := bs) hv' with ⟨b, hb, hvb⟩
      have hidx :
          ∃ i : Fin bs.length, v ∈ (bs.get i).2.2.freeVars := by
        have : ∃ b ∈ bs, v ∈ b.2.2.freeVars := ⟨b, hb, hvb⟩
        simpa using (List.exists_mem_iff_get (l := bs) (p := fun b => v ∈ b.2.2.freeVars)).1 this
/- ## Structured Block 7 -/
      rcases hidx with ⟨i, hvi⟩
      have hchild : childRel (toCoind (.send p bs)) (toCoind (bs.get i).2.2) :=
        child_rel_to_coind_send (p := p) (bs := bs) i
      have hmem_child : toCoind (bs.get i).2.2 ∈ all := mem_of_closed_child h_closed hmem hchild
      exact free_vars_subset_names_in (t := (bs.get i).2.2) (all := all) h_closed hmem_child v hvi
  -- free_vars_subset_names_in: recv case
  | recv p bs =>
      intro v hv
      have hv' : v ∈ SessionTypes.LocalTypeR.freeVarsOfBranches bs := by
        simpa [LocalTypeR.freeVars] using hv
      rcases mem_free_vars_of_branches (bs := bs) hv' with ⟨b, hb, hvb⟩
      have hidx :
          ∃ i : Fin bs.length, v ∈ (bs.get i).2.2.freeVars := by
        have : ∃ b ∈ bs, v ∈ b.2.2.freeVars := ⟨b, hb, hvb⟩
        simpa using (List.exists_mem_iff_get (l := bs) (p := fun b => v ∈ b.2.2.freeVars)).1 this
      rcases hidx with ⟨i, hvi⟩
      have hchild : childRel (toCoind (.recv p bs)) (toCoind (bs.get i).2.2) :=
        child_rel_to_coind_recv (p := p) (bs := bs) i
      have hmem_child : toCoind (bs.get i).2.2 ∈ all := mem_of_closed_child h_closed hmem hchild
      exact free_vars_subset_names_in (t := (bs.get i).2.2) (all := all) h_closed hmem_child v hvi
termination_by sizeOf t
decreasing_by
  all_goals
    cases t <;> rename_i h <;> cases h;
      first
      | exact (size_of_body_lt_size_of_mu _ _)
      | exact (size_of_get_lt_size_of_send (p := _) (bs := _) _)

end SessionCoTypes.Coinductive
