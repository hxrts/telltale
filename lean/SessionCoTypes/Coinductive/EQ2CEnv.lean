import Mathlib
import Paco
import SessionCoTypes.Coinductive.LocalTypeC
import SessionCoTypes.Coinductive.EQ2C
import SessionCoTypes.Coinductive.EQ2CProps
import SessionCoTypes.Coinductive.Observable

set_option linter.dupNamespace false

/-!
The Problem. EQ2C relates coinductive types directly, but cannot handle finite
syntax with explicit variable nodes that represent back-edges. When converting
between inductive and coinductive representations, variables name cycles.

The difficulty is that these variables must be interpreted through an environment
that tracks what each name refers to. EQ2CE (environment-aware EQ2C) uses paco
(parametrized coinduction) to handle this, allowing the relation to unfold mu
nodes while recording bindings for later variable resolution.

Solution Structure.
1. Define Env and EnvPair to track name-to-node mappings
2. EnvResolves ensures environment respects EQ2C at back-edges
3. EQ2CE_step gives one-step bisimulation with environment threading
4. EQ2CE is the paco greatest fixed point of EQ2CE_step
5. EQ2CE_coind provides the coinduction principle
-/

namespace SessionCoTypes.Coinductive

open SessionTypes.GlobalType

/-! ## Environments -/

/-- Environment mapping names to a set of coinductive nodes. -/
abbrev Env := String → Set LocalTypeC

/-- Empty environment. -/
def Env.empty : Env := fun _ => ∅

/-- Insert a binding into the environment (adds to the set for that name). -/
def Env.insert (env : Env) (x : String) (v : LocalTypeC) : Env :=
  fun y => if y = x then {v} ∪ env y else env y

/-- Pair of environments for left/right sides. -/
abbrev EnvPair := Env × Env

def envL (ρ : EnvPair) : Env := ρ.1
def envR (ρ : EnvPair) : Env := ρ.2

def envInsertL (ρ : EnvPair) (x : String) (v : LocalTypeC) : EnvPair :=
  (Env.insert ρ.1 x v, ρ.2)

def envInsertR (ρ : EnvPair) (x : String) (v : LocalTypeC) : EnvPair :=
  (ρ.1, Env.insert ρ.2 x v)

/-! ## Environment resolutions (back-edge discipline) -/

/-- Environment resolves variables to EQ2C-equivalent nodes. -/
def EnvResolves (ρ : EnvPair) : Prop :=
  (∀ x c, c ∈ envL ρ x → EQ2C (mkVar x) c) ∧
  (∀ x c, c ∈ envR ρ x → EQ2C c (mkVar x))

def EnvResolvesL (ρ : EnvPair) : Prop :=
  ∀ x c, c ∈ envL ρ x → EQ2C (mkVar x) c

/-! ## Environment right-invariant (vars only) -/

/-- Right environment only stores the matching variable node. -/
def EnvVarR (ρ : EnvPair) : Prop :=
  ∀ x c, c ∈ envR ρ x → c = mkVar x

/-! ## Unfolding from environment membership -/

lemma EnvResolves_unfolds_left {ρ : EnvPair} {x : String} {c : LocalTypeC}
    (hρ : EnvResolves ρ) (hmem : c ∈ envL ρ x) : UnfoldsToVarC c x := by
  exact EQ2C_mkVar_left_unfolds (hρ.1 _ _ hmem)

lemma EnvResolves_unfolds_right {ρ : EnvPair} {x : String} {c : LocalTypeC}
    (hρ : EnvResolves ρ) (hmem : c ∈ envR ρ x) : UnfoldsToVarC c x := by
  exact EQ2C_mkVar_right_unfolds (hρ.2 _ _ hmem)

lemma EnvResolvesL_unfolds {ρ : EnvPair} {x : String} {c : LocalTypeC}
    (hρ : EnvResolvesL ρ) (hmem : c ∈ envL ρ x) : UnfoldsToVarC c x := by
  exact EQ2C_mkVar_left_unfolds (hρ _ _ hmem)

/-! ## EnvResolves preservation under insert -/

lemma EnvResolves_insertL {ρ : EnvPair} {x : String} {b : LocalTypeC}
    (hρ : EnvResolves ρ) (hvar : EQ2C (mkVar x) b) :
    EnvResolves (envInsertL ρ x b) := by
  constructor
  · intro y c hmem
    by_cases hy : y = x
    · -- y = x case
      simp only [envInsertL, envL, Env.insert, hy, ↓reduceIte, Set.mem_union,
        Set.mem_singleton_iff] at hmem
      cases hmem with
      | inl hcb =>
          rw [hcb, hy]; exact hvar
      | inr hmem' =>
          rw [hy]; exact hρ.1 _ _ hmem'
    · -- y ≠ x case
      simp only [envInsertL, envL, Env.insert, hy, ↓reduceIte] at hmem
      exact hρ.1 _ _ hmem
  · intro y c hmem
    simp only [envInsertL, envR] at hmem
    exact hρ.2 _ _ hmem

lemma EnvResolves_insertR {ρ : EnvPair} {x : String} {a : LocalTypeC}
    (hρ : EnvResolves ρ) (hvar : EQ2C a (mkVar x)) :
    EnvResolves (envInsertR ρ x a) := by
  constructor
  · intro y c hmem
    simp only [envInsertR, envL] at hmem
    exact hρ.1 _ _ hmem
  · intro y c hmem
    by_cases hy : y = x
    · -- y = x case
      simp only [envInsertR, envR, Env.insert, hy, ↓reduceIte, Set.mem_union,
        Set.mem_singleton_iff] at hmem
      cases hmem with
      | inl hca =>
          rw [hca, hy]; exact hvar
      | inr hmem' =>
          rw [hy]; exact hρ.2 _ _ hmem'
    · -- y ≠ x case
      simp only [envInsertR, envR, Env.insert, hy, ↓reduceIte] at hmem
      exact hρ.2 _ _ hmem

lemma EnvResolves_insertL_mem {ρ : EnvPair} {x : String} {b : LocalTypeC}
    (hρ : EnvResolves ρ) (hmem : b ∈ envL ρ x) :
    EnvResolves (envInsertL ρ x b) := by
  exact EnvResolves_insertL (ρ := ρ) (x := x) (b := b) hρ (hρ.1 _ _ hmem)

lemma EnvResolves_insertR_mem {ρ : EnvPair} {x : String} {a : LocalTypeC}
    (hρ : EnvResolves ρ) (hmem : a ∈ envR ρ x) :
    EnvResolves (envInsertR ρ x a) := by
  exact EnvResolves_insertR (ρ := ρ) (x := x) (a := a) hρ (hρ.2 _ _ hmem)

lemma EnvResolves_insertR_var {ρ : EnvPair} {x : String}
    (hρ : EnvResolves ρ) : EnvResolves (envInsertR ρ x (mkVar x)) := by
  exact EnvResolves_insertR (ρ := ρ) (x := x) (a := mkVar x) hρ (EQ2C_var x)

lemma EnvResolves_envInsertR {ρ : EnvPair} {x : String} {a : LocalTypeC}
    (hρ : EnvResolves ρ) (hvar : EQ2C a (mkVar x)) :
    EnvResolves (envInsertR ρ x a) := by
  exact EnvResolves_insertR (ρ := ρ) (x := x) (a := a) hρ hvar

lemma EnvResolvesL_insertR {ρ : EnvPair} {x : String} {a : LocalTypeC}
    (hρ : EnvResolvesL ρ) : EnvResolvesL (envInsertR ρ x a) := by
  intro y c hmem
  have hmem' : c ∈ envL ρ y := by
    simpa [envInsertR] using hmem
  exact hρ _ _ hmem'

/-! ## EnvVarR preservation -/

lemma EnvVarR_insertL {ρ : EnvPair} {x : String} {b : LocalTypeC}
    (hρ : EnvVarR ρ) : EnvVarR (envInsertL ρ x b) := by
  intro y c hmem
  simp only [envInsertL, envR] at hmem
  exact hρ _ _ hmem

lemma EnvVarR_insertR_var {ρ : EnvPair} {x : String}
    (hρ : EnvVarR ρ) : EnvVarR (envInsertR ρ x (mkVar x)) := by
  intro y c hmem
  by_cases hy : y = x
  · have hmem' : c = mkVar x ∨ c ∈ envR ρ x := by
      simpa [envInsertR, envR, Env.insert, hy, Set.mem_union, Set.mem_singleton_iff] using hmem
    cases hmem' with
    | inl hc => simpa [hy] using hc
    | inr hc =>
        have hc' : c ∈ envR ρ y := by
          simpa [hy] using hc
        exact hρ _ _ hc'
  · have hmem' : c ∈ envR ρ y := by
      simpa [envInsertR, envR, Env.insert, hy, Set.mem_singleton_iff, false_or] using hmem
    exact hρ _ _ hmem'

lemma EnvResolves_of_left_varR {ρ : EnvPair}
    (hL : EnvResolvesL ρ) (hR : EnvVarR ρ) : EnvResolves ρ := by
  constructor
  · exact hL
  · intro x c hmem
    have hc : c = mkVar x := hR _ _ hmem
    subst hc
    exact EQ2C_var x

lemma EnvResolvesL_insertL_mem {ρ : EnvPair} {x : String} {b : LocalTypeC}
    (hρ : EnvResolvesL ρ) (hmem : b ∈ envL ρ x) :
    EnvResolvesL (envInsertL ρ x b) := by
  intro y c hmem'
  by_cases hy : y = x
  · -- y = x case
    subst hy
    -- hmem' : c ∈ envL (envInsertL ρ y b) y = c ∈ {b} ∪ envL ρ y
    simp only [envInsertL, envL, Env.insert, ↓reduceIte, Set.mem_union,
      Set.mem_singleton_iff] at hmem'
    cases hmem' with
    | inl hcb =>
        subst hcb
        exact hρ _ _ hmem
    | inr hmem'' =>
        exact hρ _ _ hmem''
  · -- y ≠ x case: envL (envInsertL ρ x b) y = envL ρ y
    simp only [envInsertL, envL, Env.insert, hy, ↓reduceIte] at hmem'
    exact hρ _ _ hmem'

/-! ## Branch relation (env-aware) -/

abbrev Rel := EnvPair → LocalTypeC → LocalTypeC → Prop
abbrev State := EnvPair × LocalTypeC × LocalTypeC
abbrev StateRel := Paco.Rel State

def toPacoRel (R : Rel) : StateRel :=
  fun s t => s = t ∧ R s.1 s.2.1 s.2.2

def fromPacoRel (R : StateRel) : Rel :=
  fun ρ a b => R (ρ, a, b) (ρ, a, b)

@[simp] lemma fromPacoRel_toPacoRel (R : Rel) :
    fromPacoRel (toPacoRel R) = R := by
  funext ρ a b
  simp [fromPacoRel, toPacoRel]

def BranchesRelCE (R : Rel) (ρ : EnvPair)
    (bs cs : List (Label × LocalTypeC)) : Prop :=
  List.Forall₂ (fun b c => b.1 = c.1 ∧ R ρ b.2 c.2) bs cs

lemma BranchesRelCE_mono {R S : Rel} (h : ∀ ρ a b, R ρ a b → S ρ a b) :
    ∀ {ρ bs cs}, BranchesRelCE R ρ bs cs → BranchesRelCE S ρ bs cs := by
  intro ρ bs cs hrel
  exact List.Forall₂.imp (fun a b hab => ⟨hab.1, h _ _ _ hab.2⟩) hrel

lemma BranchesRelCE_to_C_fixed {R : Rel} {ρ : EnvPair} {bs cs : List (Label × LocalTypeC)}
    (h : BranchesRelCE R ρ bs cs) :
    BranchesRelC (fun a b => R ρ a b) bs cs := by
  refine List.Forall₂.imp ?_ h
  intro b c hbc
  exact ⟨hbc.1, hbc.2⟩

/-! ## One-step environment-aware bisimulation -/

inductive EQ2CE_step (R : Rel) (ρ : EnvPair) (a b : LocalTypeC) : Prop
  | end
      (ha : head a = .end) (hb : head b = .end) :
      EQ2CE_step R ρ a b
  | send {p labels labels'}
      (ha : head a = .send p labels)
      (hb : head b = .send p labels')
      (hbr : BranchesRelCE R ρ (branchesOf a) (branchesOf b)) :
      EQ2CE_step R ρ a b
  | recv {p labels labels'}
      (ha : head a = .recv p labels)
      (hb : head b = .recv p labels')
      (hbr : BranchesRelCE R ρ (branchesOf a) (branchesOf b)) :
      EQ2CE_step R ρ a b
  | var {x : String}
      (ha : head a = .var x) (hb : head b = .var x) :
      EQ2CE_step R ρ a b
  | var_left {x}
      (ha : head a = .var x)
      (hmem : b ∈ envL ρ x) :
      EQ2CE_step R ρ a b
  | var_right {x}
      (hb : head b = .var x)
      (hmem : a ∈ envR ρ x) :
      EQ2CE_step R ρ a b
  | mu_left {x f}
      (ha : PFunctor.M.dest a = ⟨LocalTypeHead.mu x, f⟩)
      (hmem : b ∈ envL ρ x)
      (hrel : R (envInsertL ρ x b) (f ()) b) :
      EQ2CE_step R ρ a b
  | mu_right {x f}
      (hb : PFunctor.M.dest b = ⟨LocalTypeHead.mu x, f⟩)
      (hrel : R (envInsertR ρ x (mkVar x)) a (f ())) :
      EQ2CE_step R ρ a b

def EQ2CE_step_paco (R : StateRel) : StateRel :=
  fun s t =>
    s = t ∧ EQ2CE_step (fromPacoRel R) s.1 s.2.1 s.2.2

lemma EQ2CE_step_mono : Paco.Monotone2 EQ2CE_step_paco := by
  intro R S h s t hrel
  rcases hrel with ⟨hst, hstep⟩
  subst hst
  refine ⟨rfl, ?_⟩
  cases hstep with
  | «end» ha hb => exact EQ2CE_step.«end» ha hb
  | send ha hb hbr =>
      exact EQ2CE_step.send ha hb (BranchesRelCE_mono (fun ρ a b hr => h _ _ hr) hbr)
  | recv ha hb hbr =>
      exact EQ2CE_step.recv ha hb (BranchesRelCE_mono (fun ρ a b hr => h _ _ hr) hbr)
  | var ha hb =>
      exact EQ2CE_step.var ha hb
  | var_left ha hmem =>
      exact EQ2CE_step.var_left ha hmem
  | var_right hb hmem =>
      exact EQ2CE_step.var_right hb hmem
  | mu_left ha hmem hrel =>
      exact EQ2CE_step.mu_left ha hmem (h _ _ hrel)
  | mu_right hb hrel =>
      exact EQ2CE_step.mu_right hb (h _ _ hrel)

def EQ2CEFMono : Paco.MonoRel State where
  F := EQ2CE_step_paco
  mono := EQ2CE_step_mono

/-! ## Environment-aware coinductive equality (paco) -/

def EQ2CE (ρ : EnvPair) (a b : LocalTypeC) : Prop :=
  Paco.paco EQ2CEFMono ⊥ (ρ, a, b) (ρ, a, b)

/-- fromPacoRel (paco EQ2CEFMono ⊥) equals EQ2CE by definition. -/
lemma fromPacoRel_paco_eq_EQ2CE :
    fromPacoRel (Paco.paco EQ2CEFMono ⊥) = EQ2CE := by
  funext ρ a b
  rfl

lemma EQ2CE_unfold {ρ : EnvPair} {a b : LocalTypeC} (h : EQ2CE ρ a b) :
    EQ2CE_step EQ2CE ρ a b := by
  have h' := Paco.paco_unfold EQ2CEFMono ⊥ (ρ, a, b) (ρ, a, b) h
  rcases h' with ⟨_, hstep⟩
  -- upaco ⊥ = paco ⊥
  simp only [Paco.upaco_bot] at hstep
  -- fromPacoRel (paco ...) = EQ2CE
  rw [fromPacoRel_paco_eq_EQ2CE] at hstep
  exact hstep

/-! ## Coinduction helpers -/

/-- fromPacoRel (toPacoRel R ⊔ ⊥) = R -/
@[simp] lemma fromPacoRel_toPacoRel_sup_bot (R : Rel) :
    fromPacoRel (toPacoRel R ⊔ ⊥) = R := by
  funext ρ a b
  simp only [fromPacoRel, toPacoRel, sup_bot_eq, true_and]

theorem EQ2CE_coind {R : Rel}
    (hpost : ∀ ρ a b, R ρ a b → EQ2CE_step R ρ a b) :
    ∀ ρ a b, R ρ a b → EQ2CE ρ a b := by
  intro ρ a b hR
  have hR' : toPacoRel R (ρ, a, b) (ρ, a, b) := ⟨rfl, hR⟩
  apply Paco.paco_coind EQ2CEFMono (toPacoRel R) ⊥
  · intro s t hrel
    rcases hrel with ⟨hst, hrel⟩
    subst hst
    have hstep := hpost _ _ _ hrel
    -- EQ2CEFMono.F (toPacoRel R ⊔ ⊥) s s = s = s ∧ EQ2CE_step (fromPacoRel (toPacoRel R ⊔ ⊥)) ...
    -- Since fromPacoRel (toPacoRel R ⊔ ⊥) = R, we can use hstep
    simp only [EQ2CEFMono, EQ2CE_step_paco, fromPacoRel_toPacoRel_sup_bot]
    exact ⟨trivial, hstep⟩
  · exact hR'

end SessionCoTypes.Coinductive
