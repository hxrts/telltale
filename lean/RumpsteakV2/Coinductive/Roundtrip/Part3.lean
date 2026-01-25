import RumpsteakV2.Coinductive.Roundtrip.Part2

set_option linter.dupNamespace false

namespace RumpsteakV2.Coinductive
/-! ## Stub Definitions (Work in Progress)

These definitions and theorems are incomplete. Full proofs are being developed
in this file. The placeholders below serve as notes for the public API.
-/

/-- Name assigned to a coinductive node in a finite system. -/
noncomputable def nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String :=
  match head c with
  | .mu x => x
  | _     => nameFor c all

/-- Environment generated from a finite system of nodes. -/
def envOf (all : Finset LocalTypeC) (_visited : Finset LocalTypeC) : EnvPair :=
  (fun x => { c | c ∈ all ∧ nameOf c all = x }, fun x => { mkVar x })

/-! ## envOf containment helpers -/

def EnvOfSub (all : Finset LocalTypeC) (ρ : EnvPair) : Prop :=
  ∀ x c, c ∈ all → nameOf c all = x → c ∈ envL ρ x

lemma envOf_sub (all visited : Finset LocalTypeC) : EnvOfSub all (envOf all visited) := by
  intro x c hmem hname
  simp [envOf, envL, hmem, hname]

lemma EnvOfSub_insertL {all : Finset LocalTypeC} {ρ : EnvPair} (x : String) (v : LocalTypeC)
    (hsub : EnvOfSub all ρ) : EnvOfSub all (envInsertL ρ x v) := by
  intro y c hmem hname
  have hc : c ∈ envL ρ y := hsub y c hmem hname
  by_cases hy : y = x
  · subst hy
    -- envL after insert: {v} ∪ envL ρ y
    have h' : c = v ∨ c ∈ envL ρ y := Or.inr hc
    simpa [envInsertL, envL, Env.insert] using h'
  · simpa [envInsertL, envL, Env.insert, hy] using hc

lemma EnvOfSub_insertR {all : Finset LocalTypeC} {ρ : EnvPair} (x : String) (v : LocalTypeC)
    (hsub : EnvOfSub all ρ) : EnvOfSub all (envInsertR ρ x v) := by
  intro y c hmem hname
  have hc : c ∈ envL ρ y := hsub y c hmem hname
  simpa [envInsertR, envL] using hc

lemma EnvOfSub_mem {all : Finset LocalTypeC} {ρ : EnvPair} {c : LocalTypeC}
    (hsub : EnvOfSub all ρ) (hmem : c ∈ all) : c ∈ envL ρ (nameOf c all) :=
  hsub (nameOf c all) c hmem rfl

lemma nameOf_ne_var_of_head_var {all : Finset LocalTypeC} {b : LocalTypeC} {x : String}
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
  exact (nameFor_not_mem_namesIn b all) hx'

lemma branchesOf_toCoind_send_ofFn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    branchesOf (toCoind (.send p (List.ofFn f))) =
      List.ofFn (fun i => ((f i).1, toCoind (f i).2)) := by
  simp [branchesOf_mkSend, toCoindBranches_ofFn]

lemma branchesOf_toCoind_recv_ofFn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    branchesOf (toCoind (.recv p (List.ofFn f))) =
      List.ofFn (fun i => ((f i).1, toCoind (f i).2)) := by
  simp [branchesOf_mkRecv, toCoindBranches_ofFn]

lemma head_toCoind_send_ofFn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    head (toCoind (.send p (List.ofFn f))) =
      .send p (List.ofFn fun i => (f i).1) := by
  have hcomp :
      (Prod.fst ∘ fun i => ((f i).1, toCoind (f i).2)) = fun i => (f i).1 := by
    funext i
    rfl
  simp [head_mkSend, toCoindBranches_ofFn, List.map_ofFn, hcomp]

lemma head_toCoind_recv_ofFn {p : String} {n : Nat}
    (f : Fin n → (Label × LocalTypeR)) :
    head (toCoind (.recv p (List.ofFn f))) =
      .recv p (List.ofFn fun i => (f i).1) := by
  have hcomp :
      (Prod.fst ∘ fun i => ((f i).1, toCoind (f i).2)) = fun i => (f i).1 := by
    funext i
    rfl
  simp [head_mkRecv, toCoindBranches_ofFn, List.map_ofFn, hcomp]

lemma envOf_varR (all visited : Finset LocalTypeC) : EnvVarR (envOf all visited) := by
  intro x c hmem
  simpa [envOf] using hmem

lemma envOf_resolvesL_of_backedge {all visited : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolvesL (envOf all visited) := by
  intro x c hmem
  have hmem' : c ∈ all ∧ nameOf c all = x := by
    simpa [envOf] using hmem
  rcases hmem' with ⟨hmem_all, hname⟩
  have h := hback c hmem_all
  simpa [hname] using h

lemma envOf_resolves_of_backedge {all visited : Finset LocalTypeC}
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    EnvResolves (envOf all visited) :=
  EnvResolves_of_left_varR (envOf_resolvesL_of_backedge (all := all) (visited := visited) hback)
    (envOf_varR all visited)

end RumpsteakV2.Coinductive.Roundtrip
