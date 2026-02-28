import SessionCoTypes.Coinductive.Roundtrip.PacoCollapse

set_option linter.dupNamespace false

/-! # SessionCoTypes.Coinductive.Roundtrip.EnvDefs

Environment naming (nameOf, envOf), containment helpers, and toInductiveBody.
-/

/-
The Problem. Converting from coinductive to inductive types requires generating
fresh names and tracking them in an environment. We need definitions for naming
nodes and building environments, plus containment helpers for correctness proofs.

Solution Structure. Defines `nameOf` assigning names to coinductive nodes (using
existing mu-binder names or generating fresh ones). `envOf` builds an environment
from a finite system of nodes. `EnvOfSub` and helpers prove containment properties
needed for round-trip correctness. `toInductiveBody` handles the body conversion.
-/

namespace SessionCoTypes.Coinductive
open SessionTypes.GlobalType
open SessionTypes.LocalTypeR
local instance : DecidableEq LocalTypeC := by
  classical
  infer_instance
/-! ## Environment Naming and Containment

Core definitions for assigning names to coinductive nodes and building environments.
-/

/-- Name assigned to a coinductive node in a finite system. -/
def nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String :=
  match head c with
  | .mu x => x
  | _     => nameFor c all

/-- Environment generated from a finite system of nodes. -/
def envOf (all : Finset LocalTypeC) (_visited : Finset LocalTypeC) : EnvPair :=
  (fun x => { c | c ∈ all ∧ nameOf c all = x }, fun x => { mkVar x })

/-! ## envOf containment helpers -/

def EnvOfSub (all : Finset LocalTypeC) (ρ : EnvPair) : Prop :=
  ∀ x c, c ∈ all → nameOf c all = x → c ∈ envL ρ x

lemma env_of_sub (all visited : Finset LocalTypeC) : EnvOfSub all (envOf all visited) := by
  intro x c hmem hname
  simp [envOf, envL, hmem, hname]

lemma env_of_sub_insert_l {all : Finset LocalTypeC} {ρ : EnvPair} (x : String) (v : LocalTypeC)
    (hsub : EnvOfSub all ρ) : EnvOfSub all (envInsertL ρ x v) := by
  intro y c hmem hname
  have hc : c ∈ envL ρ y := hsub y c hmem hname
  by_cases hy : y = x
  · subst hy
    -- envL after insert: {v} ∪ envL ρ y
    have h' : c = v ∨ c ∈ envL ρ y := Or.inr hc
    simpa [envInsertL, envL, Env.insert] using h'
  · simpa [envInsertL, envL, Env.insert, hy] using hc

lemma env_of_sub_insert_r {all : Finset LocalTypeC} {ρ : EnvPair} (x : String) (v : LocalTypeC)
    (hsub : EnvOfSub all ρ) : EnvOfSub all (envInsertR ρ x v) := by
  intro y c hmem hname
  have hc : c ∈ envL ρ y := hsub y c hmem hname
  simpa [envInsertR, envL] using hc

lemma env_of_sub_mem {all : Finset LocalTypeC} {ρ : EnvPair} {c : LocalTypeC}
    (hsub : EnvOfSub all ρ) (hmem : c ∈ all) : c ∈ envL ρ (nameOf c all) :=
  hsub (nameOf c all) c hmem rfl

lemma name_of_ne_var_of_head_var {all : Finset LocalTypeC} {b : LocalTypeC} {x : String}
    (hb : head b = .var x) (hmem : b ∈ all) : nameOf b all ≠ x := by
  classical
  have hname : nameOf b all = nameFor b all := by
    simp [nameOf, hb]
  have hx : x ∈ namesIn all := by
    have hx' : x ∈ namesOf b := by
      simp [namesOf, hb]
    exact Finset.mem_biUnion.2 ⟨b, hmem, hx'⟩
  intro h_eq
  have h_eq' : nameFor b all = x := by
    simpa [hname] using h_eq
  have hx' : nameFor b all ∈ namesIn all := by
    simpa [h_eq'] using hx
  exact (name_for_not_mem_names_in b all) hx'

/-! ## toCoind Branch and Head Helpers -/

lemma branches_of_to_coind_send_of_fn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    branchesOf (toCoind (.send p (List.ofFn f))) =
      List.ofFn (fun i => ((f i).1, toCoind (f i).2)) := by
  simp [branches_of_mk_send, to_coind_branches_of_fn]

lemma branches_of_to_coind_recv_of_fn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    branchesOf (toCoind (.recv p (List.ofFn f))) =
      List.ofFn (fun i => ((f i).1, toCoind (f i).2)) := by
  simp [branches_of_mk_recv, to_coind_branches_of_fn]

lemma head_to_coind_send_of_fn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    head (toCoind (.send p (List.ofFn f))) =
      .send p (List.ofFn fun i => (f i).1) := by
  have hcomp :
      (Prod.fst ∘ fun i => ((f i).1, toCoind (f i).2)) = fun i => (f i).1 := by
    funext i
    rfl
  simp [head_mk_send, to_coind_branches_of_fn, List.map_ofFn, hcomp]

lemma head_to_coind_recv_of_fn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    head (toCoind (.recv p (List.ofFn f))) =
      .recv p (List.ofFn fun i => (f i).1) := by
  have hcomp :
      (Prod.fst ∘ fun i => ((f i).1, toCoind (f i).2)) = fun i => (f i).1 := by
    funext i
    rfl
  simp [head_mk_recv, to_coind_branches_of_fn, List.map_ofFn, hcomp]

/-! ## envOf Resolution Lemmas -/

lemma env_of_var_r (all visited : Finset LocalTypeC) : EnvVarR (envOf all visited) := by
  intro x c hmem
  simpa [envOf] using hmem

lemma env_of_resolves_l_of_backedge {all visited : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolvesL (envOf all visited) := by
  intro x c hmem
  have hmem' : c ∈ all ∧ nameOf c all = x := by
    simpa [envOf] using hmem
  rcases hmem' with ⟨hmem_all, hname⟩
  have h := hback c hmem_all
  simpa [hname] using h

lemma env_of_resolves_of_backedge {all visited : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolves (envOf all visited) :=
  env_resolves_of_left_var_r (env_of_resolves_l_of_backedge (all := all) (visited := visited) hback)
    (env_of_var_r all visited)

/-! ## toInductive body helper -/

/-- Canonical unfold body for toInductiveAux. -/
def toInductiveBody (root : LocalTypeC) (all visited : Finset LocalTypeC)
    (current : LocalTypeC)
    (h_closed : IsClosedSet all)
    (h_visited : visited ⊆ all) (h_current : current ∈ all) : LocalTypeR :=
  let visited' := Insert.insert current visited
  match hdest : PFunctor.M.dest current with
  | ⟨.end, _⟩   => LocalTypeR.end
  | ⟨.var x, _⟩ => LocalTypeR.var x
  | ⟨.mu x, k⟩  =>
      let child := k ()
      have hchild : childRel current child := ⟨.mu x, k, (), hdest, rfl⟩
      have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
      toInductiveAux root all visited' child h_closed
        (subset_insert_of_mem h_current h_visited) hchild_mem
  | ⟨.send p labels, k⟩ =>
      let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
        let child := k i
        have hchild : childRel current child := ⟨.send p labels, k, i, hdest, rfl⟩
        have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
        let body := toInductiveAux root all visited' child h_closed
          (subset_insert_of_mem h_current h_visited) hchild_mem
        (labels[i], body)
      LocalTypeR.send p (List.ofFn f)
  | ⟨.recv p labels, k⟩ =>
      let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
        let child := k i
        have hchild : childRel current child := ⟨.recv p labels, k, i, hdest, rfl⟩
        have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
        let body := toInductiveAux root all visited' child h_closed
          (subset_insert_of_mem h_current h_visited) hchild_mem
        (labels[i], body)
      LocalTypeR.recv p (List.ofFn f)

/-! ## toInductiveBody Expansion Lemma -/

lemma to_inductive_body_eq_match (root : LocalTypeC) (all visited : Finset LocalTypeC)
    (current : LocalTypeC)
    (h_closed : IsClosedSet all)
    (h_visited : visited ⊆ all) (h_current : current ∈ all) :
    toInductiveBody root all visited current h_closed h_visited h_current =
      (match hdest : PFunctor.M.dest current with
      | ⟨.end, _⟩   => LocalTypeR.end
      | ⟨.var x, _⟩ => LocalTypeR.var x
      | ⟨.mu x, k⟩  =>
          let child := k ()
          have hchild : childRel current child := ⟨.mu x, k, (), hdest, rfl⟩
          have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
          toInductiveAux root all (Insert.insert current visited) child h_closed
            (subset_insert_of_mem h_current h_visited) hchild_mem
      | ⟨.send p labels, k⟩ =>
          let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
            let child := k i
            have hchild : childRel current child := ⟨.send p labels, k, i, hdest, rfl⟩
            have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
            let body := toInductiveAux root all (Insert.insert current visited) child h_closed
              (subset_insert_of_mem h_current h_visited) hchild_mem
            (labels[i], body)
          LocalTypeR.send p (List.ofFn f)
      | ⟨.recv p labels, k⟩ =>
          let f : Fin labels.length → (Label × LocalTypeR) := fun i =>
            let child := k i
            have hchild : childRel current child := ⟨.recv p labels, k, i, hdest, rfl⟩
            have hchild_mem : child ∈ all := mem_of_closed_child h_closed h_current hchild
            let body := toInductiveAux root all (Insert.insert current visited) child h_closed
              (subset_insert_of_mem h_current h_visited) hchild_mem
            (labels[i], body)
          LocalTypeR.recv p (List.ofFn f)) := by
  rfl

end SessionCoTypes.Coinductive
