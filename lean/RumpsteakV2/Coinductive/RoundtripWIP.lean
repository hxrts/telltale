import Mathlib
import RumpsteakV2.Coinductive.LocalTypeC
import RumpsteakV2.Coinductive.Bridge
import RumpsteakV2.Coinductive.ToInductive
import RumpsteakV2.Coinductive.ToCoindInjectivity
import RumpsteakV2.Coinductive.RoundtripHelpers
import RumpsteakV2.Coinductive.EQ2C
import RumpsteakV2.Coinductive.EQ2CEnv
import RumpsteakV2.Coinductive.EQ2CPaco
import RumpsteakV2.Protocol.LocalTypeR

set_option linter.dupNamespace false

/-
The Problem. Full round-trip correctness theorems are incomplete:
1. toInductiveAux_toCoind: proof doesn't match current toInductiveAux definition
2. EQ2CE_to_EQ2C_paco/post: coinductive proofs need paco-style reasoning
3. RoundtripRel_postfix: postfixpoint property incomplete
4. toInductiveAux_eq2c: EQ2C preservation incomplete

Current Status: These proofs use `sorry` or `admit` and need revision to
align with the updated `toInductiveAux` definition in ToInductive.lean.

Dependencies:
- ToCoindInjectivity.lean: injectivity proofs (working)
- RoundtripHelpers.lean: helper lemmas (working)
- ToInductive.lean: current toInductiveAux definition
-/

namespace RumpsteakV2.Coinductive

open Classical
open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR

/-! ## EQ2CE → EQ2C erasure (paco-style, incomplete) -/

def EQ2CE_rel (a b : LocalTypeC) : Prop :=
  ∃ ρ, EnvResolvesL ρ ∧ EnvVarR ρ ∧ EQ2CE ρ a b

theorem EQ2CE_to_EQ2C_paco {a b : LocalTypeC} (hR : EQ2CE_rel a b) :
    EQ2C_paco a b := by
  -- TODO: coinductive proof via paco
  sorry

theorem EQ2CE_to_EQ2C_post {a b : LocalTypeC} (hR : EQ2CE_rel a b) :
    EQ2C_step_paco (EQ2CE_rel ⊔ EQ2C_paco) a b := by
  -- TODO: coinduction step
  sorry

theorem EQ2CE_to_EQ2C {ρ : EnvPair} {a b : LocalTypeC}
    (hce : EQ2CE ρ a b) (hEnvL : EnvResolvesL ρ) (hVarR : EnvVarR ρ) :
    EQ2C a b := by
  have hR : EQ2CE_rel a b := ⟨ρ, hEnvL, hVarR, hce⟩
  exact paco_to_EQ2C (EQ2CE_to_EQ2C_paco hR)

/-! ## toInductiveBody (auxiliary definition) -/

/-- Body computation used by `toInductiveAux` when `current ∉ visited`.
    Note: This definition may not match current toInductiveAux exactly. -/
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

/-! ## toInductiveAux_toCoind (BROKEN - needs revision)

The proof below was written for an older version of `toInductiveAux`.
The current definition in ToInductive.lean has different mu-wrapping logic
at the end that needs to be accounted for.
-/

-- theorem toInductiveAux_toCoind :
--     ∀ (t : LocalTypeR) (all visited : Finset LocalTypeC)
--       (h_closed : IsClosedSet all) (h_visited : visited ⊆ all)
--       (h_current : toCoind t ∈ all) (hvis : VisitedLt t visited),
--       toInductiveAux (toCoind t) all visited (toCoind t) h_closed h_visited h_current = t := by
--   -- BROKEN: The proof structure doesn't match current toInductiveAux definition
--   sorry

/-! ## toInductive_toCoind (depends on broken proof above) -/

-- theorem toInductive_toCoind (t : LocalTypeR) :
--     toInductive (toCoind t) (toCoind_regular t) = t := by
--   -- Depends on toInductiveAux_toCoind which is broken
--   sorry

/-! ## nameOf and envOf definitions -/

/-- Name used by `toInductiveAux` for a given coinductive node. -/
noncomputable def nameOf (c : LocalTypeC) (all : Finset LocalTypeC) : String :=
  match head c with
  | .mu x => x
  | _ => nameFor c all

/-- Environment generated from a visited set (left-only, right empty). -/
def envOf (all visited : Finset LocalTypeC) : EnvPair :=
  (fun x => {c | c ∈ visited ∧ nameOf c all = x}, Env.empty)

/-! ## envOf lemmas -/

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

/-! ## Environment insertion lemmas -/

lemma EnvResolvesL_insertL_nameOf {all : Finset LocalTypeC} {ρ : EnvPair} {b : LocalTypeC}
    (hEnv : EnvResolvesL ρ)
    (hmem : b ∈ envL ρ (nameOf b all)) :
    EnvResolvesL (envInsertL ρ (nameOf b all) b) := by
  exact EnvResolvesL_insertL_mem (ρ := ρ) (x := nameOf b all) (b := b) hEnv hmem

lemma EnvResolvesL_insertL_nameOf_of_backedge {all : Finset LocalTypeC} {ρ : EnvPair}
    {b : LocalTypeC}
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

/-! ## EnvContains predicate -/

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

/-! ## RoundtripRel (bisimulation candidate) -/

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

/-! ## Main round-trip theorems (INCOMPLETE) -/

theorem RoundtripRel_postfix {root : LocalTypeC} {all : Finset LocalTypeC}
    (h_closed : IsClosedSet all) :
    ∀ ρ a b, RoundtripRel root all h_closed ρ a b →
      EQ2CE_step (RoundtripRel root all h_closed) ρ a b := by
  -- TODO: needs careful case analysis on toInductiveAux/toInductiveBody
  sorry

attribute [-simp] toInductiveAux.eq_1

theorem toInductiveAux_eq2c (root : LocalTypeC) (all : Finset LocalTypeC) (b : LocalTypeC)
    (h_closed : IsClosedSet all)
    (hback : ∀ c ∈ all, EQ2C (mkVar (nameOf c all)) c) :
    ∀ visited (h_visited : visited ⊆ all) (h_current : b ∈ all),
      EQ2C (toCoind (toInductiveAux root all visited b h_closed h_visited h_current)) b := by
  -- TODO: induction on visited size, case analysis on b
  sorry

/-! ## Final round-trip theorems -/

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
