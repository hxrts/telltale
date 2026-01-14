import Mathlib
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Observable
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CProps
import RumpsteakV2.Coinductive.EQ2CPaco
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.WellFormed
import RumpsteakV2.Coinductive.RegularityLemmas
import RumpsteakV2.Coinductive.ToCoindRegular
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-!
# Round-trip helpers for LocalTypeC/LocalTypeR

Auxiliary lemmas used in the inductive/coinductive round-trip proofs.
-/

namespace RumpsteakV2.Coinductive

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open Classical

/-! ## `toCoind` injectivity -/

mutual
  theorem toCoind_injective : ∀ {t u : LocalTypeR}, toCoind t = toCoind u → t = u
    | .end, .end, _ => rfl
    | .end, .var _, h => by
        cases (congrArg head h)
    | .end, .mu _ _, h => by
        cases (congrArg head h)
    | .end, .send _ _, h => by
        cases (congrArg head h)
    | .end, .recv _ _, h => by
        cases (congrArg head h)
    | .var _, .end, h => by
        cases (congrArg head h)
    | .var x, .var y, h => by
        have hhead := congrArg head h
        have hx : x = y := by
          simpa [head_mkVar] using hhead
        subst hx
        rfl
    | .var _, .mu _ _, h => by
        cases (congrArg head h)
    | .var _, .send _ _, h => by
        cases (congrArg head h)
    | .var _, .recv _ _, h => by
        cases (congrArg head h)
    | .mu _ _, .end, h => by
        cases (congrArg head h)
    | .mu _ _, .var _, h => by
        cases (congrArg head h)
    | .mu x body, .mu y body', h => by
        have hdest := congrArg PFunctor.M.dest h
        simp [toCoind, mkMu, -Sigma.mk.inj_iff] at hdest
        have hxhy := (Sigma.mk.inj_iff.mp hdest)
        have hx : x = y := by
          cases hxhy.1
          rfl
        subst hx
        have hfun : (fun _ : Unit => toCoind body) = (fun _ : Unit => toCoind body') := by
          exact eq_of_heq hxhy.2
        have hchild : toCoind body = toCoind body' := by
          simpa using congrArg (fun f => f ()) hfun
        exact congrArg (LocalTypeR.mu x) (toCoind_injective hchild)
    | .mu _ _, .send _ _, h => by
        cases (congrArg head h)
    | .mu _ _, .recv _ _, h => by
        cases (congrArg head h)
    | .send _ _, .end, h => by
        cases (congrArg head h)
    | .send _ _, .var _, h => by
        cases (congrArg head h)
    | .send _ _, .mu _ _, h => by
        cases (congrArg head h)
    | .send p bs, .send q cs, h => by
        have hhead := congrArg head h
        have hhead' : p = q ∧ (toCoindBranches bs).map Prod.fst =
            (toCoindBranches cs).map Prod.fst := by
          simpa [toCoind, head_mkSend] using hhead
        have hpq : p = q := hhead'.1
        subst hpq
        have hbranches : toCoindBranches bs = toCoindBranches cs := by
          have h' := congrArg branchesOf h
          simpa [toCoind, branchesOf_mkSend] using h'
        have hbs : bs = cs := toCoindBranches_injective hbranches
        subst hbs
        rfl
    | .send _ _, .recv _ _, h => by
        cases (congrArg head h)
    | .recv _ _, .end, h => by
        cases (congrArg head h)
    | .recv _ _, .var _, h => by
        cases (congrArg head h)
    | .recv _ _, .mu _ _, h => by
        cases (congrArg head h)
    | .recv _ _, .send _ _, h => by
        cases (congrArg head h)
    | .recv p bs, .recv q cs, h => by
        have hhead := congrArg head h
        have hhead' : p = q ∧ (toCoindBranches bs).map Prod.fst =
            (toCoindBranches cs).map Prod.fst := by
          simpa [toCoind, head_mkRecv] using hhead
        have hpq : p = q := hhead'.1
        subst hpq
        have hbranches : toCoindBranches bs = toCoindBranches cs := by
          have h' := congrArg branchesOf h
          simpa [toCoind, branchesOf_mkRecv] using h'
        have hbs : bs = cs := toCoindBranches_injective hbranches
        subst hbs
        rfl

  theorem toCoindBranches_injective :
      ∀ {bs cs : List (Label × LocalTypeR)}, toCoindBranches bs = toCoindBranches cs → bs = cs
    | [], [], _ => rfl
    | [], _ :: _, h => by
        simpa [toCoindBranches] using h
    | _ :: _, [], h => by
        simpa [toCoindBranches] using h
    | (lb, t) :: bs, (lc, u) :: cs, h => by
        have hcons :
            (lb, toCoind t) = (lc, toCoind u) ∧
              toCoindBranches bs = toCoindBranches cs := by
          simpa [toCoindBranches] using h
        rcases hcons with ⟨hhead, htail⟩
        have hlabel : lb = lc := congrArg Prod.fst hhead
        have ht : t = u := toCoind_injective (congrArg Prod.snd hhead)
        subst hlabel
        subst ht
        have hrest : bs = cs := toCoindBranches_injective htail
        subst hrest
        rfl

end

/-! ## `toCoindBranches` indexing -/

lemma toCoindBranches_length (bs : List (Label × LocalTypeR)) :
    (toCoindBranches bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons _ _ ih =>
      simp [toCoindBranches, ih]

lemma toCoindBranches_get {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    (toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i) =
      ((bs.get i).1, toCoind (bs.get i).2) := by
  induction bs with
  | nil =>
      exact (Fin.elim0 i)
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero =>
          cases b with
          | mk label cont =>
              simp [toCoindBranches, castFin, toCoindBranches_length]
      | succ i =>
          simpa [castFin, toCoindBranches_length] using ih i

lemma toCoindBranches_get_snd {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i)).2 =
      toCoind (bs.get i).2 := by
  simpa using congrArg Prod.snd (toCoindBranches_get (bs := bs) i)

lemma labels_get_eq {bs : List (Label × LocalTypeR)} (i : Fin (bs.map Prod.fst).length) :
    (bs.map Prod.fst).get i = (bs.get (castFin (by simp) i)).1 := by
  induction bs with
  | nil =>
      exact (Fin.elim0 i)
  | cons b bs ih =>
      cases i using Fin.cases with
      | zero =>
          cases b with
          | mk label cont =>
              simp [castFin]
      | succ i =>
          simpa [castFin] using ih i

/-! ## Children of `toCoind` are themselves `toCoind` -/

lemma childRel_toCoind {t : LocalTypeR} {c : LocalTypeC}
    (h : childRel (toCoind t) c) : ∃ u : LocalTypeR, c = toCoind u := by
  cases t with
  | «end» =>
      rcases childRel_to_children h with ⟨i, _⟩
      cases i
  | var x =>
      rcases childRel_to_children h with ⟨i, _⟩
      cases i
  | mu x body =>
      rcases childRel_to_children h with ⟨i, hi⟩
      cases i
      refine ⟨body, ?_⟩
      -- The unique child of a `mu` node is its body.
      simpa [toCoind, children, mkMu] using hi.symm
  | send p bs =>
      rcases childRel_to_children h with ⟨i, hi⟩
      have hi' : children (mkSend p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mkSend] using hi'
      let i' : Fin bs.length :=
        castFin (toCoindBranches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2, ?_⟩
      have hcont :
          ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i')).2 =
            toCoind (bs.get i').2 := by
        simpa using toCoindBranches_get_snd (bs := bs) i'
      have hidx :
          castFin (by simp) i =
            castFin (toCoindBranches_length bs).symm i' := by
        cases i
        simp [i', castFin]
      simpa [hchild, hidx] using hcont
  | recv p bs =>
      rcases childRel_to_children h with ⟨i, hi⟩
      have hi' : children (mkRecv p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mkRecv] using hi'
      let i' : Fin bs.length :=
        castFin (toCoindBranches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2, ?_⟩
      have hcont :
          ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i')).2 =
            toCoind (bs.get i').2 := by
        simpa using toCoindBranches_get_snd (bs := bs) i'
      have hidx :
          castFin (by simp) i =
            castFin (toCoindBranches_length bs).symm i' := by
        cases i
        simp [i', castFin]
      simpa [hchild, hidx] using hcont

/-! ## Size bounds for `toCoind` children -/

@[simp] lemma sizeOf_get_lt_sizeOf_branches {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    sizeOf (bs.get i).2 < sizeOf bs := by
  induction bs with
  | nil =>
      exact (Fin.elim0 i)
  | cons head tail ih =>
      cases i using Fin.cases with
      | zero =>
          cases head with
          | mk label cont =>
              simpa using (sizeOf_cont_lt_sizeOf_branches label cont tail)
      | succ i =>
          have hlt := ih i
          have htail : sizeOf tail < sizeOf (head :: tail) :=
            sizeOf_tail_lt_sizeOf_branches head tail
          exact lt_trans hlt htail

@[simp] lemma sizeOf_get_lt_sizeOf_send {p : String} {bs : List (Label × LocalTypeR)}
    (i : Fin bs.length) :
    sizeOf (bs.get i).2 < sizeOf (LocalTypeR.send p bs) := by
  exact lt_trans (sizeOf_get_lt_sizeOf_branches i) (sizeOf_branches_lt_sizeOf_send p bs)

@[simp] lemma sizeOf_get_lt_sizeOf_recv {p : String} {bs : List (Label × LocalTypeR)}
    (i : Fin bs.length) :
    sizeOf (bs.get i).2 < sizeOf (LocalTypeR.recv p bs) := by
  exact lt_trans (sizeOf_get_lt_sizeOf_branches i) (sizeOf_branches_lt_sizeOf_recv p bs)

@[simp] lemma sizeOf_get_lt_of_send_eq {t : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (i : Fin bs.length)
    (h : t = LocalTypeR.send p bs) :
    sizeOf (bs.get i).2 < sizeOf t := by
  subst h
  simpa using (sizeOf_get_lt_sizeOf_send (p := p) (bs := bs) i)

@[simp] lemma sizeOf_get_lt_of_recv_eq {t : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (i : Fin bs.length)
    (h : t = LocalTypeR.recv p bs) :
    sizeOf (bs.get i).2 < sizeOf t := by
  subst h
  simpa using (sizeOf_get_lt_sizeOf_recv (p := p) (bs := bs) i)


lemma childRel_toCoind_size {t : LocalTypeR} {c : LocalTypeC}
    (h : childRel (toCoind t) c) :
    ∃ u : LocalTypeR, c = toCoind u ∧ sizeOf u < sizeOf t := by
  cases t with
  | «end» =>
      rcases childRel_to_children h with ⟨i, _⟩
      cases i
  | var x =>
      rcases childRel_to_children h with ⟨i, _⟩
      cases i
  | mu x body =>
      rcases childRel_to_children h with ⟨i, hi⟩
      cases i
      refine ⟨body, ?_, ?_⟩
      · simpa [toCoind, children, mkMu] using hi.symm
      · simpa using (sizeOf_body_lt_sizeOf_mu x body)
  | send p bs =>
      rcases childRel_to_children h with ⟨i, hi⟩
      have hi' : children (mkSend p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mkSend] using hi'
      let i' : Fin bs.length :=
        castFin (toCoindBranches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2, ?_, ?_⟩
      · have hcont :
            ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i')).2 =
              toCoind (bs.get i').2 := by
          simpa using toCoindBranches_get_snd (bs := bs) i'
        have hidx :
            castFin (by simp) i =
              castFin (toCoindBranches_length bs).symm i' := by
          cases i
          rfl
        simpa [hchild, hidx] using hcont
      · have hlt : sizeOf (bs.get i').2 < sizeOf bs := sizeOf_get_lt_sizeOf_branches i'
        exact lt_trans hlt (sizeOf_branches_lt_sizeOf_send p bs)
  | recv p bs =>
      rcases childRel_to_children h with ⟨i, hi⟩
      have hi' : children (mkRecv p (toCoindBranches bs)) i = c := by
        simpa [toCoind] using hi
      have hchild : c = ((toCoindBranches bs).get (castFin (by simp) i)).2 := by
        symm
        simpa [children_mkRecv] using hi'
      let i' : Fin bs.length :=
        castFin (toCoindBranches_length bs) (castFin (by simp) i)
      refine ⟨(bs.get i').2, ?_, ?_⟩
      · have hcont :
            ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i')).2 =
              toCoind (bs.get i').2 := by
          simpa using toCoindBranches_get_snd (bs := bs) i'
        have hidx :
            castFin (by simp) i =
              castFin (toCoindBranches_length bs).symm i' := by
          cases i
          rfl
        simpa [hchild, hidx] using hcont
      · have hlt : sizeOf (bs.get i').2 < sizeOf bs := sizeOf_get_lt_sizeOf_branches i'
        exact lt_trans hlt (sizeOf_branches_lt_sizeOf_recv p bs)

/-! ## Round-trip helpers (visited invariants + name hygiene) -/

/-- Visited nodes correspond to strictly larger inductive terms. -/
def VisitedLt (t : LocalTypeR) (visited : Finset LocalTypeC) : Prop :=
  ∀ c ∈ visited, ∃ u : LocalTypeR, c = toCoind u ∧ sizeOf t < sizeOf u

lemma visitedLt_not_mem {t : LocalTypeR} {visited : Finset LocalTypeC}
    (hvis : VisitedLt t visited) : toCoind t ∉ visited := by
  intro hmem
  rcases hvis _ hmem with ⟨u, hu, hlt⟩
  have : t = u := toCoind_injective hu
  subst this
  exact lt_irrefl _ hlt

lemma visitedLt_insert {t u : LocalTypeR} {visited : Finset LocalTypeC}
    (hsize : sizeOf u < sizeOf t) (hvis : VisitedLt t visited) :
    VisitedLt u (Insert.insert (toCoind t) visited) := by
  intro c hc
  have hc' := Finset.mem_insert.mp hc
  cases hc' with
  | inl hct =>
      exact ⟨t, hct, hsize⟩
  | inr hc =>
      rcases hvis _ hc with ⟨u', hu', hlt⟩
      exact ⟨u', hu', lt_trans hsize hlt⟩

lemma childRel_toCoind_mu {x : String} {body : LocalTypeR} :
    childRel (toCoind (.mu x body)) (toCoind body) := by
  refine ⟨.mu x, (fun _ => toCoind body), (), ?_, rfl⟩
  rfl

lemma childRel_toCoind_send {p : String} {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    childRel (toCoind (.send p bs)) (toCoind (bs.get i).2) := by
  refine ⟨head (toCoind (.send p bs)), children (toCoind (.send p bs)), ?_, rfl, ?_⟩
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [toCoindBranches_length]
    exact castFin hlen.symm i
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [toCoindBranches_length]
    have hchild' := children_mkSend p (toCoindBranches bs) (castFin hlen.symm i)
    have hcont :
        ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i)).2 =
          toCoind (bs.get i).2 := by
      simpa using toCoindBranches_get_snd (bs := bs) i
    have hidx :
        castFin (by simp) (castFin hlen.symm i) =
          castFin (toCoindBranches_length bs).symm i := by
      ext
      rfl
    have hchild :
        children (toCoind (.send p bs)) (castFin hlen.symm i) =
          ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i)).2 := by
      simpa [toCoind, hidx, -children_mkSend] using hchild'
    exact hchild.trans hcont

lemma childRel_toCoind_recv {p : String} {bs : List (Label × LocalTypeR)} (i : Fin bs.length) :
    childRel (toCoind (.recv p bs)) (toCoind (bs.get i).2) := by
  refine ⟨head (toCoind (.recv p bs)), children (toCoind (.recv p bs)), ?_, rfl, ?_⟩
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [toCoindBranches_length]
    exact castFin hlen.symm i
  ·
    have hlen : ((toCoindBranches bs).map Prod.fst).length = bs.length := by
      simp [toCoindBranches_length]
    have hchild' := children_mkRecv p (toCoindBranches bs) (castFin hlen.symm i)
    have hcont :
        ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i)).2 =
          toCoind (bs.get i).2 := by
      simpa using toCoindBranches_get_snd (bs := bs) i
    have hidx :
        castFin (by simp) (castFin hlen.symm i) =
          castFin (toCoindBranches_length bs).symm i := by
      ext
      rfl
    have hchild :
        children (toCoind (.recv p bs)) (castFin hlen.symm i) =
          ((toCoindBranches bs).get (castFin (toCoindBranches_length bs).symm i)).2 := by
      simpa [toCoind, hidx, -children_mkRecv] using hchild'
    exact hchild.trans hcont

lemma mem_freeVarsOfBranches {bs : List (Label × LocalTypeR)} {v : String} :
    v ∈ Protocol.LocalTypeR.freeVarsOfBranches bs → ∃ b ∈ bs, v ∈ b.2.freeVars := by
  induction bs with
  | nil =>
      intro hv
      cases hv
  | cons b bs ih =>
      intro hv
      simp [Protocol.LocalTypeR.freeVarsOfBranches] at hv
      cases hv with
      | inl h =>
          exact ⟨b, by simp, h⟩
      | inr h =>
          rcases ih h with ⟨b', hb', hv'⟩
          exact ⟨b', by simp [hb'], hv'⟩

lemma freeVars_subset_namesIn {t : LocalTypeR} {all : Finset LocalTypeC}
    (h_closed : IsClosedSet all) (hmem : toCoind t ∈ all) :
    ∀ v, v ∈ t.freeVars → v ∈ namesIn all := by
  classical
  cases t with
  | «end» =>
      intro v hv
      simpa [LocalTypeR.freeVars] using hv
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
        childRel_toCoind_mu (x := x) (body := body)
      have hbody_mem : toCoind body ∈ all := mem_of_closed_child h_closed hmem hchild
      have hv' : v ∈ body.freeVars := by
        have hv'' : v ∈ body.freeVars ∧ v ≠ x := by
          simpa [LocalTypeR.freeVars] using hv
        exact hv''.1
      exact freeVars_subset_namesIn (t := body) (all := all) h_closed hbody_mem v hv'
  | send p bs =>
      intro v hv
      have hv' : v ∈ Protocol.LocalTypeR.freeVarsOfBranches bs := by
        simpa [LocalTypeR.freeVars] using hv
      rcases mem_freeVarsOfBranches (bs := bs) hv' with ⟨b, hb, hvb⟩
      have hidx :
          ∃ i : Fin bs.length, v ∈ (bs.get i).2.freeVars := by
        have : ∃ b ∈ bs, v ∈ b.2.freeVars := ⟨b, hb, hvb⟩
        simpa using (List.exists_mem_iff_get (l := bs) (p := fun b => v ∈ b.2.freeVars)).1 this
      rcases hidx with ⟨i, hvi⟩
      have hchild : childRel (toCoind (.send p bs)) (toCoind (bs.get i).2) :=
        childRel_toCoind_send (p := p) (bs := bs) i
      have hmem_child : toCoind (bs.get i).2 ∈ all := mem_of_closed_child h_closed hmem hchild
      exact freeVars_subset_namesIn (t := (bs.get i).2) (all := all) h_closed hmem_child v hvi
  | recv p bs =>
      intro v hv
      have hv' : v ∈ Protocol.LocalTypeR.freeVarsOfBranches bs := by
        simpa [LocalTypeR.freeVars] using hv
      rcases mem_freeVarsOfBranches (bs := bs) hv' with ⟨b, hb, hvb⟩
      have hidx :
          ∃ i : Fin bs.length, v ∈ (bs.get i).2.freeVars := by
        have : ∃ b ∈ bs, v ∈ b.2.freeVars := ⟨b, hb, hvb⟩
        simpa using (List.exists_mem_iff_get (l := bs) (p := fun b => v ∈ b.2.freeVars)).1 this
      rcases hidx with ⟨i, hvi⟩
      have hchild : childRel (toCoind (.recv p bs)) (toCoind (bs.get i).2) :=
        childRel_toCoind_recv (p := p) (bs := bs) i
      have hmem_child : toCoind (bs.get i).2 ∈ all := mem_of_closed_child h_closed hmem hchild
      exact freeVars_subset_namesIn (t := (bs.get i).2) (all := all) h_closed hmem_child v hvi
termination_by sizeOf t
decreasing_by
  all_goals
    first
    | simpa [*] using (sizeOf_body_lt_sizeOf_mu x body)
    | simpa [*] using (sizeOf_get_lt_sizeOf_send (p := p) (bs := bs) i)
    | simpa [*] using (sizeOf_get_lt_sizeOf_recv (p := p) (bs := bs) i)

lemma toCoindBranches_ofFn {n : Nat} (f : Fin n → (Label × LocalTypeR)) :
    toCoindBranches (List.ofFn f) =
      List.ofFn (fun i => ((f i).1, toCoind (f i).2)) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero, toCoindBranches]
  | succ n ih =>
      simp [List.ofFn_succ, toCoindBranches, ih]

lemma BranchesRelCE_ofFn {R : Rel} {ρ : EnvPair} {n : Nat}
    {f g : Fin n → (Label × LocalTypeC)}
    (h : ∀ i, (f i).1 = (g i).1 ∧ R ρ (f i).2 (g i).2) :
    BranchesRelCE R ρ (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero, BranchesRelCE]
  | succ n ih =>
      have h0 := h ⟨0, Nat.succ_pos _⟩
      have h' : ∀ i : Fin n, (f i.succ).1 = (g i.succ).1 ∧ R ρ (f i.succ).2 (g i.succ).2 := by
        intro i
        simpa using h i.succ
      rcases h0 with ⟨hlabel, hrel⟩
      simp [List.ofFn_succ, BranchesRelCE]
      exact ⟨⟨hlabel, hrel⟩, ih h'⟩

lemma BranchesRelC_ofFn {n : Nat} {f g : Fin n → (Label × LocalTypeC)}
    (h : ∀ i, (f i).1 = (g i).1 ∧ EQ2C (f i).2 (g i).2) :
    BranchesRelC EQ2C (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero =>
      simp [List.ofFn_zero, BranchesRelC]
  | succ n ih =>
      have h0 := h ⟨0, Nat.succ_pos _⟩
      have h' :
          ∀ i : Fin n, (f i.succ).1 = (g i.succ).1 ∧ EQ2C (f i.succ).2 (g i.succ).2 := by
        intro i
        simpa using h i.succ
      rcases h0 with ⟨hlabel, hrel⟩
      simp [List.ofFn_succ, BranchesRelC]
      exact ⟨⟨hlabel, hrel⟩, ih h'⟩

lemma observable_of_head_end {t : LocalTypeC} (h : head t = .end) : ObservableC t := by
  refine ObservableC.is_end ?_
  exact ⟨t, Relation.ReflTransGen.refl, h⟩

lemma observable_of_head_var {t : LocalTypeC} {v : String} (h : head t = .var v) :
    ObservableC t := by
  refine ObservableC.is_var v ?_
  exact ⟨t, Relation.ReflTransGen.refl, h⟩

lemma observable_of_head_send {t : LocalTypeC} {p : String} {labels : List Label}
    (h : head t = .send p labels) : ObservableC t := by
  refine ObservableC.is_send p (branchesOf t) ?_
  exact ⟨t, labels, Relation.ReflTransGen.refl, h, rfl⟩

lemma observable_of_head_recv {t : LocalTypeC} {p : String} {labels : List Label}
    (h : head t = .recv p labels) : ObservableC t := by
  refine ObservableC.is_recv p (branchesOf t) ?_
  exact ⟨t, labels, Relation.ReflTransGen.refl, h, rfl⟩

lemma EQ2C_end_head {a b : LocalTypeC}
    (ha : head a = .end) (hb : head b = .end) : EQ2C a b := by
  let R : LocalTypeC → LocalTypeC → Prop := fun x y => head x = .end ∧ head y = .end
  have hR : IsBisimulationC R := by
    intro x y hxy
    have obs_x : ObservableC x := observable_of_head_end hxy.1
    have obs_y : ObservableC y := observable_of_head_end hxy.2
    have hx : UnfoldsToEndC x := ⟨x, Relation.ReflTransGen.refl, hxy.1⟩
    have hy : UnfoldsToEndC y := ⟨y, Relation.ReflTransGen.refl, hxy.2⟩
    exact ⟨obs_x, obs_y, ObservableRelC.is_end hx hy⟩
  exact ⟨R, hR, ⟨ha, hb⟩⟩

lemma EQ2C_var_head {a b : LocalTypeC} {v : String}
    (ha : head a = .var v) (hb : head b = .var v) : EQ2C a b := by
  let R : LocalTypeC → LocalTypeC → Prop := fun x y => head x = .var v ∧ head y = .var v
  have hR : IsBisimulationC R := by
    intro x y hxy
    have obs_x : ObservableC x := observable_of_head_var hxy.1
    have obs_y : ObservableC y := observable_of_head_var hxy.2
    have hx : UnfoldsToVarC x v := ⟨x, Relation.ReflTransGen.refl, hxy.1⟩
    have hy : UnfoldsToVarC y v := ⟨y, Relation.ReflTransGen.refl, hxy.2⟩
    exact ⟨obs_x, obs_y, ObservableRelC.is_var v hx hy⟩
  exact ⟨R, hR, ⟨ha, hb⟩⟩

lemma EQ2C_send_head {a b : LocalTypeC} {p : String} {labels labels' : List Label}
    (ha : head a = .send p labels) (hb : head b = .send p labels')
    (hbr : BranchesRelC EQ2C (branchesOf a) (branchesOf b)) : EQ2C a b := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun x y => (x = a ∧ y = b) ∨ EQ2C x y
  have hR' : IsBisimulationC R' := by
    intro x y hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_x, obs_y, hobs⟩ := hR x y hrel
        have hobs' : ObservableRelC R' x y :=
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_x, obs_y, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨hx, hy⟩
        have hx' : head x = .send p labels := by
          simpa [hx] using ha
        have hy' : head y = .send p labels' := by
          simpa [hy] using hb
        have obs_x : ObservableC x := observable_of_head_send hx'
        have obs_y : ObservableC y := observable_of_head_send hy'
        have hbr0 : BranchesRelC R' (branchesOf a) (branchesOf b) :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        have hbr' : BranchesRelC R' (branchesOf x) (branchesOf y) := by
          simpa [hx, hy] using hbr0
        have ha_send : CanSendC x p (branchesOf x) :=
          ⟨x, labels, Relation.ReflTransGen.refl, hx', rfl⟩
        have hb_send : CanSendC y p (branchesOf y) :=
          ⟨y, labels', Relation.ReflTransGen.refl, hy', rfl⟩
        exact ⟨obs_x, obs_y,
          ObservableRelC.is_send p (branchesOf x) (branchesOf y) ha_send hb_send hbr'⟩
  exact ⟨R', hR', Or.inl ⟨rfl, rfl⟩⟩

lemma EQ2C_recv_head {a b : LocalTypeC} {p : String} {labels labels' : List Label}
    (ha : head a = .recv p labels) (hb : head b = .recv p labels')
    (hbr : BranchesRelC EQ2C (branchesOf a) (branchesOf b)) : EQ2C a b := by
  let R' : LocalTypeC → LocalTypeC → Prop :=
    fun x y => (x = a ∧ y = b) ∨ EQ2C x y
  have hR' : IsBisimulationC R' := by
    intro x y hrel
    cases hrel with
    | inr hEQ =>
        rcases hEQ with ⟨R, hR, hrel⟩
        obtain ⟨obs_x, obs_y, hobs⟩ := hR x y hrel
        have hobs' : ObservableRelC R' x y :=
          ObservableRelC_mono (fun _ _ hr => Or.inr ⟨R, hR, hr⟩) hobs
        exact ⟨obs_x, obs_y, hobs'⟩
    | inl hpair =>
        rcases hpair with ⟨hx, hy⟩
        have hx' : head x = .recv p labels := by
          simpa [hx] using ha
        have hy' : head y = .recv p labels' := by
          simpa [hy] using hb
        have obs_x : ObservableC x := observable_of_head_recv hx'
        have obs_y : ObservableC y := observable_of_head_recv hy'
        have hbr0 : BranchesRelC R' (branchesOf a) (branchesOf b) :=
          BranchesRelC_mono (fun _ _ hr => Or.inr hr) hbr
        have hbr' : BranchesRelC R' (branchesOf x) (branchesOf y) := by
          simpa [hx, hy] using hbr0
        have ha_recv : CanRecvC x p (branchesOf x) :=
          ⟨x, labels, Relation.ReflTransGen.refl, hx', rfl⟩
        have hb_recv : CanRecvC y p (branchesOf y) :=
          ⟨y, labels', Relation.ReflTransGen.refl, hy', rfl⟩
        exact ⟨obs_x, obs_y,
          ObservableRelC.is_recv p (branchesOf x) (branchesOf y) ha_recv hb_recv hbr'⟩
  exact ⟨R', hR', Or.inl ⟨rfl, rfl⟩⟩

lemma eq_of_dest_eq {a b : LocalTypeC} (h : PFunctor.M.dest a = PFunctor.M.dest b) : a = b := by
  refine PFunctor.M.bisim (R := fun x y => PFunctor.M.dest x = PFunctor.M.dest y) ?_ a b h
  intro x y hxy
  cases hx : x.dest with
  | mk a f =>
      have hy : y.dest = ⟨a, f⟩ := by
        simpa [hx] using hxy.symm
      refine ⟨a, f, f, rfl, hy, ?_⟩
      intro i
      rfl

lemma mu_eta {b : LocalTypeC} {x : String} {k : Unit → LocalTypeC}
    (hdest : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, k⟩) : b = mkMu x (k ()) := by
  have hk : k = fun _ => k () := by
    funext u
    cases u
    rfl
  have hdest' : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, fun _ => k ()⟩ := by
    have hdest' := hdest
    rw [hk] at hdest'
    exact hdest'
  exact eq_of_dest_eq hdest'

lemma EQ2CE_step_to_EQ2C {R : Rel} {ρ : EnvPair} {a b : LocalTypeC}
    (hR : ∀ ρ a b, R ρ a b → EQ2C a b)
    (hEnv : EnvResolves ρ)
    (hstep : EQ2CE_step R ρ a b) : EQ2C a b := by
  cases hstep with
  | «end» ha hb =>
      exact EQ2C_end_head ha hb
  | var ha hb =>
      exact EQ2C_var_head ha hb
  | send ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_send_head ha hb hbr'
  | recv ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_recv_head ha hb hbr'
  | var_left ha hmem =>
      rename_i x
      have hvar : EQ2C a (mkVar x) := by
        have hb : head (mkVar x) = .var x := by simp
        exact EQ2C_var_head ha hb
      exact EQ2C_trans hvar (hEnv.1 _ _ hmem)
  | var_right hb hmem =>
      rename_i x
      have hvar : EQ2C (mkVar x) b := by
        have ha : head (mkVar x) = .var x := by simp
        exact EQ2C_var_head ha hb
      exact EQ2C_trans (hEnv.2 _ _ hmem) hvar
  | mu_left ha hmem hrel =>
      rename_i x f
      have hrec : EQ2C (f ()) b := hR _ _ _ hrel
      have hmu : EQ2C (mkMu x (f ())) b := EQ2C_unfold_left hrec x
      have ha' : a = mkMu x (f ()) := mu_eta (b := a) (x := x) (k := f) ha
      simpa [ha'] using hmu
  | mu_right hb hrel =>
      rename_i x f
      have hrec : EQ2C a (f ()) := hR _ _ _ hrel
      have hmu : EQ2C a (mkMu x (f ())) := EQ2C_unfold_right hrec x
      have hb' : b = mkMu x (f ()) := mu_eta (b := b) (x := x) (k := f) hb
      simpa [hb'] using hmu

lemma EQ2CE_step_to_EQ2C_varR {R : Rel} {ρ : EnvPair} {a b : LocalTypeC}
    (hR : ∀ ρ a b, R ρ a b → EQ2C a b)
    (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ)
    (hstep : EQ2CE_step R ρ a b) : EQ2C a b := by
  have hEnv : EnvResolves ρ := EnvResolves_of_left_varR hEnvL hVarR
  exact EQ2CE_step_to_EQ2C (hR := hR) hEnv hstep

/-! ## EQ2CE → EQ2C erasure (env‑aware, paco) -/

def EQ2CE_rel (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

theorem EQ2CE_to_EQ2C_paco {a b : LocalTypeC} (hR : EQ2CE_rel a b) :
    EQ2C_paco a b := by
  -- TODO: coinductive proof via paco
  admit

theorem EQ2CE_to_EQ2C_post {a b : LocalTypeC} (hR : EQ2CE_rel a b) :
    EQ2C_step_paco (EQ2CE_rel ⊔ EQ2C_paco) a b := by
  -- TODO: coinduction step
  admit


theorem EQ2CE_to_EQ2C {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C a b := by
  have hR : EQ2CE_rel a b := ⟨ρ, hEnvL, hVarR, hce⟩
  exact paco_to_EQ2C (EQ2CE_to_EQ2C_paco hR)

lemma EQ2CE_step_to_EQ2C_left {R : Rel} {ρ : EnvPair} {a b : LocalTypeC}
    (hR : ∀ ρ a b, R ρ a b → EQ2C a b)
    (hEnv : EnvResolvesL ρ)
    (hNoRight : ∀ x, head b = .var x → a ∈ envR ρ x → False)
    (hstep : EQ2CE_step R ρ a b) : EQ2C a b := by
  cases hstep with
  | «end» ha hb =>
      exact EQ2C_end_head ha hb
  | var ha hb =>
      exact EQ2C_var_head ha hb
  | send ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_send_head ha hb hbr'
  | recv ha hb hbr =>
      have hbr0 : BranchesRelC (fun x y => R ρ x y) (branchesOf a) (branchesOf b) :=
        BranchesRelCE_to_C_fixed hbr
      have hbr' : BranchesRelC EQ2C (branchesOf a) (branchesOf b) :=
        BranchesRelC_mono (fun x y hxy => hR ρ _ _ hxy) hbr0
      exact EQ2C_recv_head ha hb hbr'
  | var_left ha hmem =>
      rename_i x
      have hvar : EQ2C a (mkVar x) := by
        have hb : head (mkVar x) = .var x := by simp
        exact EQ2C_var_head ha hb
      exact EQ2C_trans hvar (hEnv _ _ hmem)
  | var_right hb hmem =>
      rename_i x
      exact (hNoRight x hb hmem).elim
  | mu_left ha hmem hrel =>
      rename_i x f
      have hrec : EQ2C (f ()) b := hR _ _ _ hrel
      have hmu : EQ2C (mkMu x (f ())) b := EQ2C_unfold_left hrec x
      have ha' : a = mkMu x (f ()) := mu_eta (b := a) (x := x) (k := f) ha
      simpa [ha'] using hmu
  | mu_right hb hrel =>
      rename_i x f
      have hrec : EQ2C a (f ()) := hR _ _ _ hrel
      have hmu : EQ2C a (mkMu x (f ())) := EQ2C_unfold_right hrec x
      have hb' : b = mkMu x (f ()) := mu_eta (b := b) (x := x) (k := f) hb
      simpa [hb'] using hmu

/-- Body computation used by `toInductiveAux` when `current ∉ visited`. -/
noncomputable def toInductiveBody (root : LocalTypeC) (all visited : Finset LocalTypeC)
    (current : LocalTypeC)
    (h_closed : IsClosedSet all) (h_visited : visited ⊆ all) (h_current : current ∈ all) :
    LocalTypeR :=
  let visited' := Insert.insert current visited
  match hdest : PFunctor.M.dest current with
  | ⟨.end, _⟩ => LocalTypeR.end
  | ⟨.var x, _⟩ => LocalTypeR.var x
  | ⟨.mu x, k⟩ =>
      let child := k ()
      have hchild : childRel current child := by
        exact ⟨.mu x, k, (), hdest, rfl⟩
      have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
      toInductiveAux root all visited' child h_closed
        (subset_insert_of_mem h_current h_visited) hchild_mem
  | ⟨.send p labels, k⟩ =>
      let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
        let child := k i
        have hchild : childRel current child := by
          exact ⟨.send p labels, k, i, hdest, rfl⟩
        have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
        let body :=
          toInductiveAux root all visited' child
            h_closed
            (subset_insert_of_mem h_current h_visited)
            hchild_mem
        (labels.get i, body)
      LocalTypeR.send p (List.ofFn f)
  | ⟨.recv p labels, k⟩ =>
      let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
        let child := k i
        have hchild : childRel current child := by
          exact ⟨.recv p labels, k, i, hdest, rfl⟩
        have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
        let body :=
          toInductiveAux root all visited' child
            h_closed
            (subset_insert_of_mem h_current h_visited)
            hchild_mem
        (labels.get i, body)
      LocalTypeR.recv p (List.ofFn f)

theorem toInductiveAux_toCoind :
    ∀ (t : LocalTypeR) (all visited : Finset LocalTypeC)
      (h_closed : IsClosedSet all) (h_visited : visited ⊆ all)
      (h_current : toCoind t ∈ all) (hvis : VisitedLt t visited),
      toInductiveAux (toCoind t) all visited (toCoind t) h_closed h_visited h_current = t := by
  classical
  intro t
  cases t with
  | «end» =>
      intro all visited h_closed h_visited h_current hvis
      have hnot : toCoind .end ∉ visited := visitedLt_not_mem hvis
      simp [toInductiveAux, -toInductiveAux.eq_1, hnot]
  | var x =>
      intro all visited h_closed h_visited h_current hvis
      have hnot : toCoind (.var x) ∉ visited := visitedLt_not_mem hvis
      simp [toInductiveAux, -toInductiveAux.eq_1, hnot]
  | mu x body =>
      intro all visited h_closed h_visited h_current hvis
      have hnot : toCoind (.mu x body) ∉ visited := visitedLt_not_mem hvis
      have hchild : toCoind body ∈ all := by
        have hrel : childRel (toCoind (.mu x body)) (toCoind body) :=
          childRel_toCoind_mu (x := x) (body := body)
        exact mem_of_closed_child h_closed h_current hrel
      have hvis' : VisitedLt body (Insert.insert (toCoind (.mu x body)) visited) := by
        apply visitedLt_insert (t := .mu x body) (u := body)
        · simpa using (sizeOf_body_lt_sizeOf_mu x body)
        · exact hvis
      have hrec :
          toInductiveAux (toCoind body) all (Insert.insert (toCoind (.mu x body)) visited)
            (toCoind body) h_closed
            (subset_insert_of_mem h_current h_visited) hchild = body := by
        exact toInductiveAux_toCoind body all (Insert.insert (toCoind (.mu x body)) visited)
          h_closed (subset_insert_of_mem h_current h_visited) hchild hvis'
      simp [toInductiveAux, -toInductiveAux.eq_1, hnot, hrec, toCoind]
  | send p bs =>
      intro all visited h_closed h_visited h_current hvis
      have hnot : toCoind (.send p bs) ∉ visited := visitedLt_not_mem hvis
      have hbranches :
          (List.ofFn (fun i : Fin (bs.map Prod.fst).length =>
            let i' : Fin bs.length := castFin (by simp) i
            ((bs.map Prod.fst).get i,
              toInductiveAux (toCoind (bs.get i').2) all
                (Insert.insert (toCoind (.send p bs)) visited)
                (toCoind (bs.get i').2) h_closed
                (subset_insert_of_mem h_current h_visited)
                (by
                  have hrel : childRel (toCoind (.send p bs)) (toCoind (bs.get i').2) :=
                    childRel_toCoind_send (p := p) (bs := bs) i'
                  exact mem_of_closed_child h_closed h_current hrel)
                (visitedLt_insert
                  (t := .send p bs) (u := (bs.get i').2)
                  (by simpa using (sizeOf_get_lt_sizeOf_send (p := p) (bs := bs) i'))
                  hvis))))
          = bs := by
        apply List.ext_get
        · simp [List.length_ofFn]
        · intro i hi
          have i' : Fin bs.length := ⟨i, by simpa using hi⟩
          have hrec :=
            toInductiveAux_toCoind (bs.get i').2 all (Insert.insert (toCoind (.send p bs)) visited)
              h_closed (subset_insert_of_mem h_current h_visited)
              (by
                have hrel : childRel (toCoind (.send p bs)) (toCoind (bs.get i').2) :=
                  childRel_toCoind_send (p := p) (bs := bs) i'
                exact mem_of_closed_child h_closed h_current hrel)
              (visitedLt_insert
                (t := .send p bs) (u := (bs.get i').2)
                (by simpa using (sizeOf_get_lt_sizeOf_send (p := p) (bs := bs) i'))
                hvis)
          simp [List.get_ofFn, labels_get_eq, hrec]
      simp [toInductiveAux, -toInductiveAux.eq_1, hnot, hbranches]
  | recv p bs =>
      intro all visited h_closed h_visited h_current hvis
      have hnot : toCoind (.recv p bs) ∉ visited := visitedLt_not_mem hvis
      have hbranches :
          (List.ofFn (fun i : Fin (bs.map Prod.fst).length =>
            let i' : Fin bs.length := castFin (by simp) i
            ((bs.map Prod.fst).get i,
              toInductiveAux (toCoind (bs.get i').2) all
                (Insert.insert (toCoind (.recv p bs)) visited)
                (toCoind (bs.get i').2) h_closed
                (subset_insert_of_mem h_current h_visited)
                (by
                  have hrel : childRel (toCoind (.recv p bs)) (toCoind (bs.get i').2) :=
                    childRel_toCoind_recv (p := p) (bs := bs) i'
                  exact mem_of_closed_child h_closed h_current hrel)
                (visitedLt_insert
                  (t := .recv p bs) (u := (bs.get i').2)
                  (by simpa using (sizeOf_get_lt_sizeOf_recv (p := p) (bs := bs) i'))
                  hvis))))
          = bs := by
        apply List.ext_get
        · simp [List.length_ofFn]
        · intro i hi
          have i' : Fin bs.length := ⟨i, by simpa using hi⟩
          have hrec :=
            toInductiveAux_toCoind (bs.get i').2 all (Insert.insert (toCoind (.recv p bs)) visited)
              h_closed (subset_insert_of_mem h_current h_visited)
              (by
                have hrel : childRel (toCoind (.recv p bs)) (toCoind (bs.get i').2) :=
                  childRel_toCoind_recv (p := p) (bs := bs) i'
                exact mem_of_closed_child h_closed h_current hrel)
              (visitedLt_insert
                (t := .recv p bs) (u := (bs.get i').2)
                (by simpa using (sizeOf_get_lt_sizeOf_recv (p := p) (bs := bs) i'))
                hvis)
          simp [List.get_ofFn, labels_get_eq, hrec]
      simp [toInductiveAux, -toInductiveAux.eq_1, hnot, hbranches]
termination_by sizeOf t
decreasing_by
  all_goals
    first
    | simpa [*] using (sizeOf_body_lt_sizeOf_mu x body)
    | simpa [*] using (sizeOf_get_lt_sizeOf_send (p := p) (bs := bs) i')
    | simpa [*] using (sizeOf_get_lt_sizeOf_recv (p := p) (bs := bs) i')

/-! ## Round-trip: inductive → coinductive → inductive -/

theorem toInductive_toCoind (t : LocalTypeR) :
    toInductive (toCoind t) (toCoind_regular t) = t := by
  classical
  let all : Finset LocalTypeC := Set.Finite.toFinset (toCoind_regular t)
  have h_closed : IsClosedSet all := reachable_is_closed_set (toCoind t) (toCoind_regular t)
  have h_current : toCoind t ∈ all := by
    have ht : toCoind t ∈ Reachable (toCoind t) := Relation.ReflTransGen.refl
    exact (Set.Finite.mem_toFinset (toCoind_regular t)).2 ht
  have hvis : VisitedLt t (∅ : Finset LocalTypeC) := by
    intro c hc
    cases hc
  have haux := toInductiveAux_toCoind t all ∅ h_closed
    (by exact Finset.empty_subset _) h_current hvis
  simpa [toInductive, all] using haux

/-- Name used by `toInductiveAux` for a given coinductive node. -/
noncomputable def nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String :=
  match head c with
  | .mu x => x
  | _ => nameFor c all

/-- Environment generated from a visited set (left-only, right empty). -/
def envOf (all visited : Finset LocalTypeC) : EnvPair :=
  (fun x => {c | c ∈ visited ∧ nameOf c all = x}, Env.empty)

lemma envOf_mem {all visited : Finset LocalTypeC} {c : LocalTypeC} (hc : c ∈ visited) :
    c ∈ envL (envOf all visited) (nameOf c all) := by
  simp [envOf, envL, nameOf, hc]

lemma envOf_mono {all visited visited' : Finset LocalTypeC} (h : visited ⊆ visited') :
    ∀ x c, c ∈ envL (envOf all visited) x → c ∈ envL (envOf all visited') x := by
  intro x c hc
  have hc' : c ∈ visited ∧ nameOf c all = x := by
    simpa [envOf, envL] using hc
  rcases hc' with ⟨hc_mem, hc_name⟩
  have hc_mem' : c ∈ visited' := h hc_mem
  simpa [envOf, envL] using And.intro hc_mem' hc_name

lemma EnvResolves_envOf {all : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolves (envOf all all) := by
  constructor
  · intro x c hc
    have hc' : c ∈ all ∧ nameOf c all = x := by
      simpa [envOf, envL] using hc
    rcases hc' with ⟨hc_mem, hc_name⟩
    subst hc_name
    exact hback _ hc_mem
  · intro x c hc
    simp [envOf, envR, Env.empty] at hc

lemma EnvResolvesL_envOf {all : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolvesL (envOf all all) := by
  intro x c hc
  have hc' : c ∈ all ∧ nameOf c all = x := by
    simpa [envOf, envL] using hc
  rcases hc' with ⟨hc_mem, hc_name⟩
  subst hc_name
  exact hback _ hc_mem

lemma EnvVarR_envOf {all : Finset LocalTypeC} : EnvVarR (envOf all all) := by
  intro x c hc
  simp [envOf, envR, Env.empty] at hc

lemma EnvResolvesL_insertL_nameOf {all : Finset LocalTypeC} {ρ : EnvPair} {b : LocalTypeC}
    (hEnv : EnvResolvesL ρ)
    (hmem : b ∈ envL ρ (nameOf b all)) :
    EnvResolvesL (envInsertL ρ (nameOf b all) b) := by
  exact EnvResolvesL_insertL_mem (ρ := ρ) (x := nameOf b all) (b := b) hEnv hmem

lemma EnvResolvesL_insertL_nameOf_of_backedge {all : Finset LocalTypeC} {ρ : EnvPair} {b : LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c)
    (hEnv : EnvResolvesL ρ) (hb : b ∈ all) :
    EnvResolvesL (envInsertL ρ (nameOf b all) b) := by
  intro y c hmem
  by_cases hy : y = nameOf b all
  · subst hy
    have hmem' : c ∈ ({b} ∪ envL ρ (nameOf b all)) := by
      simpa [envInsertL, envL, Env.insert] using hmem
    have hmem'' : c = b ∨ c ∈ envL ρ (nameOf b all) := by
      simpa [Set.mem_union, Set.mem_singleton_iff] using hmem'
    cases hmem'' with
    | inl hcb =>
        subst hcb
        exact hback _ hb
    | inr hmem''' =>
        exact hEnv _ _ hmem'''
  · have hmem' : c ∈ envL ρ y := by
      simpa [envInsertL, envL, Env.insert, hy] using hmem
    exact hEnv _ _ hmem'

lemma EnvResolves_insertL_nameOf {all : Finset LocalTypeC} {ρ : EnvPair} {b : LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c)
    (hEnv : EnvResolves ρ) (hb : b ∈ all) :
    EnvResolves (envInsertL ρ (nameOf b all) b) := by
  exact EnvResolves_insertL (ρ := ρ) (x := nameOf b all) (b := b) hEnv (hback _ hb)

def EnvContains (all visited : Finset LocalTypeC) (ρ : EnvPair) : Prop :=
  ∀ c ∈ visited, c ∈ envL ρ (nameOf c all)

lemma envContains_envOf (all visited : Finset LocalTypeC) :
    EnvContains all visited (envOf all visited) := by
  intro c hc
  exact envOf_mem (all := all) (visited := visited) hc

lemma envContains_insert {all visited : Finset LocalTypeC} {ρ : EnvPair} {c : LocalTypeC}
    (h : EnvContains all visited ρ) :
    EnvContains all (Insert.insert c visited) (envInsertL ρ (nameOf c all) c) := by
  intro d hd
  have hd' : d = c ∨ d ∈ visited := by
    simpa [Finset.mem_insert] using hd
  cases hd' with
  | inl hdc =>
      subst hdc
      simp [envInsertL, envL, Env.insert, nameOf]
  | inr hmem =>
      have hmem' : d ∈ envL ρ (nameOf d all) := h _ hmem
      by_cases hx : nameOf d all = nameOf c all
      · have hmem'' : d ∈ envL ρ (nameOf c all) := by simpa [hx] using hmem'
        have hmemU : d ∈ ({c} ∪ envL ρ (nameOf c all)) := Or.inr hmem''
        simpa [envInsertL, envL, Env.insert, hx, Set.mem_union, Set.mem_singleton_iff] using hmemU
      · simpa [envInsertL, envL, Env.insert, hx] using hmem'

lemma envContains_insert_mem {all visited : Finset LocalTypeC} {ρ : EnvPair} {c : LocalTypeC}
    (h : EnvContains all visited ρ) :
    EnvContains all visited (envInsertL ρ (nameOf c all) c) := by
  intro d hd
  have hmem' : d ∈ envL ρ (nameOf d all) := h _ hd
  by_cases hx : nameOf d all = nameOf c all
  · have hmem'' : d ∈ envL ρ (nameOf c all) := by simpa [hx] using hmem'
    have hmemU : d ∈ ({c} ∪ envL ρ (nameOf c all)) := Or.inr hmem''
    simpa [envInsertL, envL, Env.insert, hx, Set.mem_union, Set.mem_singleton_iff] using hmemU
  · simpa [envInsertL, envL, Env.insert, hx] using hmem'

def RoundtripRel (root : LocalTypeC) (all : Finset LocalTypeC)
    (h_closed : IsClosedSet all) : Rel :=
  fun ρ a b =>
    EnvContains all all ρ ∧
    ∃ (visited : Finset LocalTypeC) (h_visited : visited ⊆ all) (h_current : b ∈ all),
      a =
        toCoind (toInductiveAux root all visited b h_closed h_visited h_current) ∨
      a =
        toCoind (toInductiveBody root all visited b h_closed h_visited h_current)

def RoundtripRelC (root : LocalTypeC) (all : Finset LocalTypeC)
    (h_closed : IsClosedSet all) (a b : LocalTypeC) : Prop :=
  ∃ ρ, RoundtripRel root all h_closed ρ a b

lemma BranchesRelCE_to_C {R : Rel} {ρ : EnvPair} {bs cs : List (Label × LocalTypeC)}
    (h : BranchesRelCE R ρ bs cs) :
    BranchesRelC (fun a b => ∃ ρ, R ρ a b) bs cs := by
  refine List.Forall₂.imp ?_ h
  intro b c hbc
  exact ⟨hbc.1, ⟨ρ, hbc.2⟩⟩

lemma RoundtripRel_toCoind {root : LocalTypeC} {all : Finset LocalTypeC}
    {h_closed : IsClosedSet all} {ρ : EnvPair} {a b : LocalTypeC}
    (h : RoundtripRel root all h_closed ρ a b) : ∃ t : LocalTypeR, a = toCoind t := by
  rcases h with ⟨_, visited, h_visited, h_current, hEq⟩
  cases hEq with
  | inl haux =>
      exact ⟨toInductiveAux root all visited b h_closed h_visited h_current, haux⟩
  | inr hbody =>
      exact ⟨toInductiveBody root all visited b h_closed h_visited h_current, hbody⟩

theorem RoundtripRel_postfix {root : LocalTypeC} {all : Finset LocalTypeC}
    (h_closed : IsClosedSet all) :
    ∀ ρ a b, RoundtripRel root all h_closed ρ a b →
      EQ2CE_step (RoundtripRel root all h_closed) ρ a b := by
  admit

attribute [-simp] toInductiveAux.eq_1

theorem toInductiveAux_eq2c (root : LocalTypeC) (all : Finset LocalTypeC) (b : LocalTypeC)
    (h_closed : IsClosedSet all)
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    ∀ visited (h_visited : visited ⊆ all) (h_current : b ∈ all),
      EQ2C (toCoind (toInductiveAux root all visited b h_closed h_visited h_current)) b := by
  admit

theorem toCoind_toInductive_eq2ce (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t := by
  classical
  let all : Finset LocalTypeC := Set.Finite.toFinset h
  have h_closed : IsClosedSet all := reachable_is_closed_set t h
  have h_current : t ∈ all := by
    have ht : t ∈ Reachable t := Relation.ReflTransGen.refl
    exact (Set.Finite.mem_toFinset h).2 ht
  have hEnv : EnvContains all all (envOf all all) := envContains_envOf all all
  have hrel : RoundtripRel t all h_closed (envOf all all) (toCoind (toInductive t h)) t := by
    refine ⟨hEnv, (∅ : Finset LocalTypeC), ?_, h_current, ?_⟩
    · exact Finset.empty_subset _
    · simp [toInductive, all]
  have hpost :
      ∀ ρ a b, RoundtripRel t all h_closed ρ a b →
        EQ2CE_step (RoundtripRel t all h_closed) ρ a b := by
    intro ρ a b hR
    exact RoundtripRel_postfix (root := t) (all := all) (h_closed := h_closed) ρ a b hR
  exact EQ2CE_coind (R := RoundtripRel t all h_closed) hpost _ _ _ hrel

theorem toCoind_toInductive_eq2c_of_eq2ce (t : LocalTypeC) (h : Regular t)
    (hback :
      ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c)
    (hce :
      EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
        (toCoind (toInductive t h)) t) :
    EQ2C (toCoind (toInductive t h)) t := by
  -- EQ2CE is the canonical round-trip statement; EQ2C is derived by erasing the env.
  have hEnvL : EnvResolvesL (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) := by
    exact EnvResolvesL_envOf (all := Set.Finite.toFinset h) hback
  have hVarR : EnvVarR (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h)) := by
    exact EnvVarR_envOf (all := Set.Finite.toFinset h)
  exact EQ2CE_to_EQ2C hce hEnvL hVarR

theorem toCoind_toInductive_eq2c_of_backedge (t : LocalTypeC) (h : Regular t)
    (hback :
      ∀ c ∈ Set.Finite.toFinset h, EQ2C (mkVar (nameOf c (Set.Finite.toFinset h))) c) :
    EQ2C (toCoind (toInductive t h)) t := by
  classical
  let all : Finset LocalTypeC := Set.Finite.toFinset h
  have h_closed : IsClosedSet all := reachable_is_closed_set t h
  have h_current : t ∈ all := by
    have ht : t ∈ Reachable t := Relation.ReflTransGen.refl
    exact (Set.Finite.mem_toFinset h).2 ht
  have haux :
      EQ2C (toCoind (toInductiveAux t all ∅ t h_closed (by exact Finset.empty_subset _) h_current)) t := by
    have hback' : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c := by
      simpa [all] using hback
    exact toInductiveAux_eq2c t all t h_closed hback' ∅ (by exact Finset.empty_subset _) h_current
  simpa [toInductive, all] using haux

theorem toCoind_toInductive_eq2c_of_env (t : LocalTypeC) (h : Regular t)
    (hEnv : EnvResolves (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))) :
    EQ2C (toCoind (toInductive t h)) t := by
  classical
  let all : Finset LocalTypeC := Set.Finite.toFinset h
  have hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c := by
    intro c hc
    have hmem : c ∈ envL (envOf all all) (nameOf c all) := envOf_mem (all := all) (visited := all) hc
    exact (hEnv.1 _ _ hmem)
  simpa [all] using toCoind_toInductive_eq2c_of_backedge t h hback

theorem toCoind_toInductive (t : LocalTypeC) (h : Regular t) :
    EQ2CE (envOf (Set.Finite.toFinset h) (Set.Finite.toFinset h))
      (toCoind (toInductive t h)) t := by
  simpa using toCoind_toInductive_eq2ce t h

end RumpsteakV2.Coinductive
