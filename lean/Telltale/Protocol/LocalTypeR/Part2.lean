import Telltale.Protocol.LocalTypeR.Part1

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-! # LocalTypeR Part 2

Environment application, active variables, closedness, and free-variable substitution properties.
-/

namespace Telltale.Protocol.LocalTypeR
open Telltale.Protocol.GlobalType
/-! ## Environments (abstraction point for closedness vs substitutions)

We model an environment as a list of (name, type) bindings and define:
- `ClosedUnder env t`: all free vars of `t` are covered by `env`
- `Env.apply env t`: apply the environment as sequential substitution

`ActiveEnv` is the single integration point. It is currently `sigmaOfVars ActiveVars`
(with `ActiveVars = []` by default),
but can later be swapped for a substitution environment without changing proofs
that go through the `*_ActiveEnv` lemmas. -/

abbrev Env := List (String × LocalTypeR)

def Env.dom : Env → List String
  | [] => []
  | (v, _) :: rest => v :: Env.dom rest

def ClosedUnder (env : Env) (lt : LocalTypeR) : Prop :=
  ∀ v, v ∈ lt.freeVars → v ∈ env.dom

def Env.apply : Env → LocalTypeR → LocalTypeR
  | [], lt => lt
  | (v, t) :: rest, lt => Env.apply rest (lt.substitute v t)

/-! ## Environment Well-Formedness

To make the substitution-environment swap safe, we track that every binding
maps to a closed, contractive type. This lets us propagate closedness and
contractiveness through Env.apply. -/

def EnvWellFormed : Env → Prop
  | [] => True
  | (_, t) :: rest => t.isClosed ∧ t.isContractive = true ∧ EnvWellFormed rest

/-! ## Parametric Sigma Environment

`sigmaOfVars S` is a canonical environment that closes exactly the variables in `S`
by mapping each to a closed, contractive type (`.end`). This is the non‑leaky,
parametric substitution environment used to swap in a sigma context. -/

def sigmaOfVars (S : List String) : Env :=
  S.map (fun v => (v, LocalTypeR.end))

theorem sigmaOfVars_dom (S : List String) :
    Env.dom (sigmaOfVars S) = S := by
  induction S with
  | nil => simp [sigmaOfVars, Env.dom]
  | cons v rest ih =>
      simp [sigmaOfVars, Env.dom]
      simpa [sigmaOfVars] using ih

theorem sigmaOfVars_wf (S : List String) : EnvWellFormed (sigmaOfVars S) := by
  induction S with
  | nil => simp [sigmaOfVars, EnvWellFormed]
  | cons v rest ih =>
      have ih' : EnvWellFormed (List.map (fun v => (v, LocalTypeR.end)) rest) := by
        simpa [sigmaOfVars] using ih
      simp [sigmaOfVars, EnvWellFormed, LocalTypeR.isClosed, LocalTypeR.isContractive, LocalTypeR.freeVars, ih']

theorem closedUnder_sigmaOfVars {S : List String} {lt : LocalTypeR}
    (hsubset : ∀ v, v ∈ lt.freeVars → v ∈ S) :
    ClosedUnder (sigmaOfVars S) lt := by
  intro v hv
  have hvS : v ∈ S := hsubset v hv
  simpa [sigmaOfVars_dom S] using hvS

def ActiveVars : List String := []

def ActiveEnv : Env := sigmaOfVars ActiveVars

abbrev ClosedUnderActive (lt : LocalTypeR) : Prop := ClosedUnder ActiveEnv lt

def applyActiveEnv (lt : LocalTypeR) : LocalTypeR :=
  Env.apply ActiveEnv lt

theorem closedUnderActive_of_closed (lt : LocalTypeR) :
    lt.isClosed → ClosedUnderActive lt := by
  intro h v hv
  have hnil : lt.freeVars = [] := by
    have : lt.freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using h
    exact (List.isEmpty_eq_true _).1 this
  have : False := by
    simpa [hnil] using hv
  exact this.elim

theorem activeEnv_wellFormed : EnvWellFormed ActiveEnv := by
  simpa [ActiveEnv] using (sigmaOfVars_wf ActiveVars)

/-! ## SubstContext: Unified Substitution Environment

`SubstContext` is the TypeContext-based representation of substitution environments,
providing a unified interface with `NameOnlyContext` from `TypeContext.lean`.

For backward compatibility, `Env` remains as `List (String × LocalTypeR)` with
bridge functions to convert between the two representations.
-/

open Telltale.Protocol

/-- Substitution context using the unified TypeContext structure. -/
abbrev SubstContext := TypeContext String LocalTypeR

namespace SubstContext

/-- Domain of a substitution context (list of variable names). -/
def dom (ctx : SubstContext) : List String := ctx.names

/-- Apply substitution context to a local type. -/
def apply (ctx : SubstContext) : LocalTypeR → LocalTypeR :=
  ctx.bindings.foldr (fun (v, t) acc => acc.substitute v t)

/-- Check if environment is well-formed (all bindings are closed and contractive). -/
def WellFormed : SubstContext → Prop
  | ⟨[]⟩ => True
  | ⟨(_, t) :: rest⟩ => t.isClosed ∧ t.isContractive = true ∧ WellFormed ⟨rest⟩

/-- Convert SubstContext to Env. -/
def toEnv (ctx : SubstContext) : Env := ctx.bindings

/-- Convert Env to SubstContext. -/
def ofEnv (env : Env) : SubstContext := ⟨env⟩

@[simp]
theorem toEnv_ofEnv (env : Env) : (ofEnv env).toEnv = env := rfl

@[simp]
theorem ofEnv_toEnv (ctx : SubstContext) : ofEnv ctx.toEnv = ctx := by
  cases ctx; rfl

theorem dom_eq_Env_dom (ctx : SubstContext) : ctx.dom = Env.dom ctx.toEnv := by
  simp only [dom, toEnv, TypeContext.names]
  induction ctx.bindings with
  | nil => rfl
  | cons hd tl ih => simp [Env.dom, ih]

end SubstContext

/-! ## ClosedUnder for the empty environment -/

theorem closedUnder_nil_iff_isClosed (lt : LocalTypeR) :
    ClosedUnder ([] : Env) lt ↔ lt.isClosed := by
  constructor
  · intro h
    have hnil : lt.freeVars = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro v hv
      have hv' : v ∈ Env.dom ([] : Env) := h v hv
      simp [Env.dom] at hv'
    simpa [LocalTypeR.isClosed, hnil] using (List.isEmpty_eq_true _).2 hnil
  · intro h v hv
    have hnil : lt.freeVars = [] := by
      have : lt.freeVars.isEmpty = true := by
        simpa [LocalTypeR.isClosed] using h
      exact (List.isEmpty_eq_true _).1 this
    have : False := by
      simpa [hnil] using hv
    exact this.elim


/-! ## Free Vars under Substitution (subset lemma) -/

mutual
  private def freeVars_substitute_subset_aux
      (lt : LocalTypeR) (varName : String) (repl : LocalTypeR)
      (x : String) (hx : x ∈ (lt.substitute varName repl).freeVars) :
      x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName) :=
    match lt with
    | .end => by
        simp [LocalTypeR.substitute, LocalTypeR.freeVars, -substituteBranches_eq_map] at hx
    | .var t => by
        by_cases h : t = varName
        · subst h
          have hbeq : (t == t) = true := by simp
          simp [LocalTypeR.substitute, hbeq, LocalTypeR.freeVars] at hx
          left; exact hx
        · have hbeq : (t == varName) = false := by
            exact (beq_eq_false_iff_ne).2 h
          have hx' : x = t := by
            simpa [LocalTypeR.substitute, hbeq, LocalTypeR.freeVars] using hx
          right
          subst hx'
          constructor
          · simp [LocalTypeR.freeVars]
          · exact h
    | .send _ bs | .recv _ bs => by
        -- Send/recv cases share the same branch substitution behavior.
        simp [LocalTypeR.substitute, LocalTypeR.freeVars, -substituteBranches_eq_map] at hx
        exact freeVars_substituteBranches_subset_aux bs varName repl x hx
    | .mu t body => by
        by_cases h : t = varName
        · -- Shadowed case
          have hbeq : (t == varName) = true := by
            simpa [beq_iff_eq] using h
          have hx' : x ∈ body.freeVars.filter (· != t) := by
            simpa [LocalTypeR.substitute, hbeq, LocalTypeR.freeVars] using hx
          right
          constructor
          · exact hx'
          · have hxne : x ≠ t := by
              have hxpair : x ∈ body.freeVars ∧ (x != t) = true := by
                simpa [List.mem_filter] using hx'
              exact (bne_iff_ne).1 hxpair.2
            simpa [h] using hxne
        · -- Not shadowed: recurse into body
          have hbeq : (t == varName) = false := by
            exact (beq_eq_false_iff_ne).2 h
          have hx' : x ∈ (body.substitute varName repl).freeVars ∧ (x != t) = true := by
            simpa [LocalTypeR.substitute, hbeq, LocalTypeR.freeVars, List.mem_filter] using hx
          have ih := freeVars_substitute_subset_aux body varName repl x hx'.1
          cases ih with
          | inl hrepl =>
              left; exact hrepl
          | inr hpair =>
              right
              constructor
              · apply (List.mem_filter).2
                exact ⟨hpair.1, hx'.2⟩
              · exact hpair.2
  termination_by sizeOf lt

  private def freeVars_substituteBranches_subset_aux
      (branches : List (Label × LocalTypeR)) (varName : String) (repl : LocalTypeR)
      (x : String) (hx : x ∈ freeVarsOfBranches (substituteBranches branches varName repl)) :
      x ∈ repl.freeVars ∨ (x ∈ freeVarsOfBranches branches ∧ x ≠ varName) :=
    match branches with
    | [] => by
        simp [substituteBranches, freeVarsOfBranches] at hx
    | (label, cont) :: rest => by
        simp [substituteBranches, freeVarsOfBranches, List.mem_append, -substituteBranches_eq_map] at hx
        cases hx with
        | inl hxcont =>
            have ih := freeVars_substitute_subset_aux cont varName repl x hxcont
            cases ih with
            | inl hrepl => left; exact hrepl
            | inr hpair =>
                right
                simp [freeVarsOfBranches, List.mem_append]
                exact ⟨Or.inl hpair.1, hpair.2⟩
        | inr hxrest =>
            have ih := freeVars_substituteBranches_subset_aux rest varName repl x hxrest
            cases ih with
            | inl hrepl => left; exact hrepl
            | inr hpair =>
                right
                simp [freeVarsOfBranches, List.mem_append]
                exact ⟨Or.inr hpair.1, hpair.2⟩
  termination_by sizeOf branches
end

theorem freeVars_substitute_subset (lt : LocalTypeR) (varName : String) (repl : LocalTypeR) :
    ∀ x, x ∈ (lt.substitute varName repl).freeVars →
         x ∈ repl.freeVars ∨ (x ∈ lt.freeVars ∧ x ≠ varName) :=
  fun x hx => freeVars_substitute_subset_aux lt varName repl x hx

theorem freeVars_substitute_closed (body : LocalTypeR) (t : String) (e : LocalTypeR) :
    e.isClosed → ∀ v, v ∈ (body.substitute t e).freeVars → v ∈ body.freeVars ∧ v ≠ t := by
  intro hclosed v hv
  have h := freeVars_substitute_subset body t e v hv
  cases h with
  | inl hrepl =>
      have hnil : e.freeVars = [] := by
        have : e.freeVars.isEmpty = true := by
          simpa [LocalTypeR.isClosed] using hclosed
        exact (List.isEmpty_eq_true _).1 this
      have : False := by
        simpa [hnil] using hrepl
      exact this.elim
  | inr hpair =>
      exact hpair


theorem freeVars_substituteBranches_closed (bs : List (Label × LocalTypeR)) (t : String) (e : LocalTypeR) :
    e.isClosed → ∀ v, v ∈ freeVarsOfBranches (substituteBranches bs t e) →
      v ∈ freeVarsOfBranches bs ∧ v ≠ t := by
  intro hclosed v hmem
  induction bs with
  | nil =>
      have : False := by
        simpa [freeVarsOfBranches] using hmem
      exact this.elim
  | cons head tail ih =>
      cases head with
      | mk label cont =>
          -- Split membership across head or tail branches
          have hmem' : v ∈ (cont.substitute t e).freeVars ∨
              v ∈ freeVarsOfBranches (substituteBranches tail t e) := by
            simpa [freeVarsOfBranches, substituteBranches, List.mem_append] using hmem
          cases hmem' with
          | inl hcont =>
              have hres := freeVars_substitute_closed cont t e hclosed v hcont
              -- v appears in head branch
              have hmem_head : v ∈ freeVarsOfBranches ((label, cont) :: tail) := by
                simp [freeVarsOfBranches, hres.1]
              exact ⟨hmem_head, hres.2⟩
          | inr htail =>
              have hres := ih htail
              have hmem_tail : v ∈ freeVarsOfBranches ((label, cont) :: tail) := by
                simp [freeVarsOfBranches, hres.1]
              exact ⟨hmem_tail, hres.2⟩

/-! ## Unfolding does not introduce new free variables -/

theorem freeVars_unfold_subset (lt : LocalTypeR) (v : String) :
    v ∈ lt.unfold.freeVars → v ∈ lt.freeVars := by
  cases lt with
  | «end» | var _ | send _ _ | recv _ _ =>
      intro hmem
      simpa [LocalTypeR.unfold] using hmem
  | mu t body =>
      intro hmem
      -- unfold = body.substitute t (.mu t body)
      have hsub := freeVars_substitute_subset body t (.mu t body) v (by simpa [LocalTypeR.unfold] using hmem)
      cases hsub with
      | inl hrepl =>
          -- repl.freeVars = body.freeVars.filter (· != t)
          have hmem' : v ∈ body.freeVars.filter (· != t) := by
            simpa [LocalTypeR.freeVars] using hrepl
          simpa [LocalTypeR.freeVars] using hmem'
      | inr hpair =>
          have hmem' : v ∈ body.freeVars.filter (· != t) := by
            apply List.mem_filter.mpr
            exact ⟨hpair.1, (bne_iff_ne).2 hpair.2⟩
          simpa [LocalTypeR.freeVars] using hmem'

theorem freeVars_iter_unfold_subset (k : Nat) (lt : LocalTypeR) (v : String) :
    v ∈ ((LocalTypeR.unfold)^[k] lt).freeVars → v ∈ lt.freeVars := by
  induction k generalizing lt with
  | zero =>
      intro hmem
      simpa using hmem
  | succ k ih =>
      intro hmem
      have hmem' : v ∈ ((LocalTypeR.unfold)^[k] lt.unfold).freeVars := by
        simpa [Function.iterate_succ_apply] using hmem
      have hmem'' := ih (lt := lt.unfold) hmem'
      exact freeVars_unfold_subset lt v hmem''

end Telltale.Protocol.LocalTypeR
