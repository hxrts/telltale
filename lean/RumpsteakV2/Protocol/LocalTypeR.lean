import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import RumpsteakV2.Protocol.GlobalType
-- Import after GlobalType to avoid circular dependencies
-- import RumpsteakV2.Protocol.LocalTypeConv

set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

/-! # RumpsteakV2.Protocol.LocalTypeR

Recursive local types for the V2 development.

## Expose

The following definitions form the semantic interface for proofs:

- `LocalTypeR`
- `LocalTypeR.dual`
- `LocalTypeR.unfold`
- `LocalTypeR.freeVars`
- `LocalTypeR.substitute`
-/

namespace RumpsteakV2.Protocol.LocalTypeR

open RumpsteakV2.Protocol.GlobalType

/-- Recursive local types with branching. -/
inductive LocalTypeR where
  | end : LocalTypeR
  | send : String → List (Label × LocalTypeR) → LocalTypeR
  | recv : String → List (Label × LocalTypeR) → LocalTypeR
  | mu : String → LocalTypeR → LocalTypeR
  | var : String → LocalTypeR
  deriving Repr, Inhabited

/- Extract free type variables from a local type. -/
mutual
  def LocalTypeR.freeVars : LocalTypeR → List String
    | .end => []
    | .send _ branches => freeVarsOfBranches branches
    | .recv _ branches => freeVarsOfBranches branches
    | .mu t body => body.freeVars.filter (· != t)
    | .var t => [t]

  def freeVarsOfBranches : List (Label × LocalTypeR) → List String
    | [] => []
    | (_, t) :: rest => t.freeVars ++ freeVarsOfBranches rest
end

/-! ## freeVars / isFreeIn bridge (converse direction)

NOTE: These theorems are moved to after the isFreeIn definition below.
-/

theorem freeVarsOfBranches_eq_flatMap (branches : List (Label × LocalTypeR)) :
    freeVarsOfBranches branches = branches.flatMap (fun (_, t) => t.freeVars) := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk label t =>
          simp [freeVarsOfBranches, ih, List.flatMap]

@[simp]
lemma sizeOf_cont_lt_sizeOf_branches (label : Label) (cont : LocalTypeR)
    (tail : List (Label × LocalTypeR)) :
    sizeOf cont < sizeOf ((label, cont) :: tail) := by
  simp +arith

@[simp]
lemma sizeOf_tail_lt_sizeOf_branches (head : Label × LocalTypeR)
    (tail : List (Label × LocalTypeR)) :
    sizeOf tail < sizeOf (head :: tail) := by
  simp +arith

@[simp]
lemma sizeOf_branches_lt_sizeOf_send (p : String) (bs : List (Label × LocalTypeR)) :
    sizeOf bs < sizeOf (LocalTypeR.send p bs) := by
  simp +arith

@[simp]
lemma sizeOf_branches_lt_sizeOf_recv (p : String) (bs : List (Label × LocalTypeR)) :
    sizeOf bs < sizeOf (LocalTypeR.recv p bs) := by
  simp +arith

@[simp]
lemma sizeOf_body_lt_sizeOf_mu (t : String) (body : LocalTypeR) :
    sizeOf body < sizeOf (LocalTypeR.mu t body) := by
  simp +arith

@[simp] lemma sizeOf_branches_lt_of_send_eq {lt : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : lt = LocalTypeR.send p bs) :
    sizeOf bs < sizeOf lt := by
  simpa [h] using sizeOf_branches_lt_sizeOf_send p bs

@[simp] lemma sizeOf_branches_lt_of_recv_eq {lt : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : lt = LocalTypeR.recv p bs) :
    sizeOf bs < sizeOf lt := by
  simpa [h] using sizeOf_branches_lt_sizeOf_recv p bs

@[simp] lemma sizeOf_body_lt_of_mu_eq {lt : LocalTypeR} {t : String} {body : LocalTypeR}
    (h : lt = LocalTypeR.mu t body) :
    sizeOf body < sizeOf lt := by
  simpa [h] using sizeOf_body_lt_sizeOf_mu t body

@[simp] lemma sizeOf_tail_lt_of_cons_eq {bs : List (Label × LocalTypeR)}
    {head : Label × LocalTypeR} {tail : List (Label × LocalTypeR)}
    (h : bs = head :: tail) :
    sizeOf tail < sizeOf bs := by
  simpa [h] using sizeOf_tail_lt_sizeOf_branches head tail

@[simp] lemma sizeOf_cont_lt_of_head_eq {bs : List (Label × LocalTypeR)}
    {head : Label × LocalTypeR} {tail : List (Label × LocalTypeR)}
    {label : Label} {cont : LocalTypeR}
    (hbs : bs = head :: tail) (hhead : head = (label, cont)) :
    sizeOf cont < sizeOf bs := by
  simpa [hbs, hhead] using sizeOf_cont_lt_sizeOf_branches label cont tail

/- Substitute a local type for a variable. -/
mutual
  def LocalTypeR.substitute : LocalTypeR → String → LocalTypeR → LocalTypeR
    | .end, _, _ => .end
    | .send partner branches, varName, replacement =>
        .send partner (substituteBranches branches varName replacement)
    | .recv partner branches, varName, replacement =>
        .recv partner (substituteBranches branches varName replacement)
    | .mu t body, varName, replacement =>
        if t == varName then
          .mu t body
        else
          .mu t (body.substitute varName replacement)
    | .var t, varName, replacement =>
        if t == varName then replacement else .var t

  def substituteBranches : List (Label × LocalTypeR) → String → LocalTypeR → List (Label × LocalTypeR)
    | [], _, _ => []
    | (label, cont) :: rest, varName, replacement =>
        (label, cont.substitute varName replacement) ::
          substituteBranches rest varName replacement
end

/-- substituteBranches is equivalent to mapping substitute over the continuations. -/
@[simp]
theorem substituteBranches_eq_map (bs : List (Label × LocalTypeR)) (var : String) (repl : LocalTypeR) :
    substituteBranches bs var repl = bs.map (fun (l, c) => (l, c.substitute var repl)) := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      simp only [substituteBranches, List.map_cons, ih]

/-! ## Basic Substitution Simplification Lemmas -/

/-- Substitution on end is always end. -/
@[simp]
theorem substitute_end (var : String) (repl : LocalTypeR) :
    LocalTypeR.end.substitute var repl = .end := rfl

/-- Substitution on send reduces to substituting on branches. -/
@[simp]
theorem substitute_send (partner : String) (branches : List (Label × LocalTypeR))
    (var : String) (repl : LocalTypeR) :
    (LocalTypeR.send partner branches).substitute var repl
    = .send partner (substituteBranches branches var repl) := rfl

/-- Substitution on recv reduces to substituting on branches. -/
@[simp]
theorem substitute_recv (partner : String) (branches : List (Label × LocalTypeR))
    (var : String) (repl : LocalTypeR) :
    (LocalTypeR.recv partner branches).substitute var repl
    = .recv partner (substituteBranches branches var repl) := rfl

/-- Unfold one level of recursion: μt.T ↦ T[μt.T/t]. -/
def LocalTypeR.unfold : LocalTypeR → LocalTypeR
  | lt@(.mu t body) => body.substitute t lt
  | lt => lt

/- Dualize a local type by swapping send/recv. -/
mutual
  def LocalTypeR.dual : LocalTypeR → LocalTypeR
    | .end => .end
    | .send partner branches => .recv partner (dualBranches branches)
    | .recv partner branches => .send partner (dualBranches branches)
    | .mu t body => .mu t (body.dual)
    | .var t => .var t

  def dualBranches : List (Label × LocalTypeR) → List (Label × LocalTypeR)
    | [] => []
    | (label, cont) :: rest => (label, cont.dual) :: dualBranches rest
end

mutual
  /-- Dual is an involution on local types. -/
  def LocalTypeR.dual_dual : (t : LocalTypeR) → t.dual.dual = t
    | .end => rfl
    | .var _ => rfl
    | .mu _ body => congrArg (LocalTypeR.mu _) body.dual_dual
    | .send _ bs => congrArg (LocalTypeR.send _) (dualBranches_dualBranches bs)
    | .recv _ bs => congrArg (LocalTypeR.recv _) (dualBranches_dualBranches bs)

  /-- Dual branches is an involution. -/
  def dualBranches_dualBranches : (bs : List (Label × LocalTypeR)) →
      dualBranches (dualBranches bs) = bs
    | [] => rfl
    | (_, cont) :: rest =>
        congrArg₂ List.cons
          (congrArg₂ Prod.mk rfl cont.dual_dual)
          (dualBranches_dualBranches rest)
end

/-! ## Dual-Substitute Commutation

These lemmas show that dual and substitute commute, which is essential for
proving that EQ2 is a congruence for duality. -/

mutual
  /-- Dual commutes with substitute: (t.substitute v r).dual = t.dual.substitute v r.dual. -/
  theorem LocalTypeR.dual_substitute : (t : LocalTypeR) → (var : String) → (repl : LocalTypeR) →
      (t.substitute var repl).dual = t.dual.substitute var repl.dual
    | .end, _, _ => rfl
    | .var v, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        split <;> rfl
    | .mu v body, var, repl =>
        if hv : v == var then by
          -- Shadowed case: both sides reduce to mu v body.dual
          simp only [LocalTypeR.substitute, LocalTypeR.dual, hv, ↓reduceIte]
        else by
          -- Non-shadowed case
          simp only [LocalTypeR.substitute, LocalTypeR.dual, hv, ↓reduceIte, Bool.false_eq_true]
          exact congrArg (LocalTypeR.mu v) (LocalTypeR.dual_substitute body var repl)
    | .send p bs, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        exact congrArg (LocalTypeR.recv p) (dualBranches_substituteBranches bs var repl)
    | .recv p bs, var, repl => by
        simp only [LocalTypeR.substitute, LocalTypeR.dual]
        exact congrArg (LocalTypeR.send p) (dualBranches_substituteBranches bs var repl)

  /-- Dual and substitute commute for branch lists. -/
  theorem dualBranches_substituteBranches : (bs : List (Label × LocalTypeR)) →
      (var : String) → (repl : LocalTypeR) →
      dualBranches (substituteBranches bs var repl) =
        substituteBranches (dualBranches bs) var repl.dual
    | [], _, _ => rfl
    | (label, cont) :: rest, var, repl => by
        simp only [substituteBranches, dualBranches]
        exact congrArg₂ List.cons
          (congrArg₂ Prod.mk rfl (LocalTypeR.dual_substitute cont var repl))
          (dualBranches_substituteBranches rest var repl)
end

/-! ## Closedness Predicate (Coq-style `eclosed`)

A local type is closed if it has no free type variables.
This matches Coq's `eclosed e := forall n, n \notin lType_fv e`. -/

theorem List.isEmpty_eq_true {α : Type} (l : List α) : l.isEmpty = true ↔ l = [] := by
  cases l <;> simp

/-- A local type is closed if it has no free type variables. -/
def LocalTypeR.isClosed (lt : LocalTypeR) : Bool := lt.freeVars.isEmpty

/-! ## Guardedness Predicate (Coq-style `eguarded`)

A variable is guarded in a type if it only appears inside a communication (send/recv).
This is the key property for proving termination of mu-unfolding.

Follows Coq's `eguarded n e` which checks if variable n is guarded at depth n. -/

mutual
  /-- Check if a variable appears free in a local type. -/
  def LocalTypeR.isFreeIn (v : String) : LocalTypeR → Bool
    | .end => false
    | .var w => v == w
    | .send _ bs => isFreeInBranches' v bs
    | .recv _ bs => isFreeInBranches' v bs
    | .mu t body => if v == t then false else body.isFreeIn v

  /-- Helper: check if variable appears free in any branch. -/
  def isFreeInBranches' (v : String) : List (Label × LocalTypeR) → Bool
    | [] => false
    | (_, c) :: rest => c.isFreeIn v || isFreeInBranches' v rest
end

/-! ## freeVars / isFreeIn bridge lemmas -/

mutual
  theorem mem_freeVars_isFreeIn (lt : LocalTypeR) (v : String) :
      v ∈ lt.freeVars → lt.isFreeIn v = true := by
    intro hmem
    cases hlt : lt with
    | «end» =>
        simp [LocalTypeR.freeVars, hlt] at hmem
    | var w =>
        have hv : v = w := by
          simpa [LocalTypeR.freeVars, hlt] using hmem
        subst hv
        simp [LocalTypeR.isFreeIn, hlt]
    | send _ bs | recv _ bs =>
        -- Send and recv cases are identical (symmetric under duality)
        have h' : v ∈ freeVarsOfBranches bs := by
          simpa [LocalTypeR.freeVars, hlt] using hmem
        have hmem' := mem_freeVarsOfBranches_isFreeInBranches' bs v h'
        simpa [LocalTypeR.isFreeIn, hlt] using hmem'
    | mu t body =>
        have h' : v ∈ body.freeVars.filter (· != t) := by
          simpa [LocalTypeR.freeVars, hlt] using hmem
        have hpair : v ∈ body.freeVars ∧ (v != t) = true := by
          simpa [List.mem_filter] using h'
        have hvne : v ≠ t := (bne_iff_ne).1 hpair.2
        have hbody : body.isFreeIn v = true := mem_freeVars_isFreeIn body v hpair.1
        have hvne' : (v == t) = false := beq_eq_false_iff_ne.mpr hvne
        simpa [LocalTypeR.isFreeIn, hvne', hlt] using hbody
  termination_by sizeOf lt
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega

  theorem mem_freeVarsOfBranches_isFreeInBranches' (bs : List (Label × LocalTypeR)) (v : String) :
      v ∈ freeVarsOfBranches bs → isFreeInBranches' v bs = true := by
    intro hmem
    cases hbs : bs with
    | nil =>
        simp [freeVarsOfBranches, hbs] at hmem
    | cons head tail =>
        cases hhead : head with
        | mk label cont =>
            have hmem' : v ∈ cont.freeVars ∨ v ∈ freeVarsOfBranches tail := by
              simpa [freeVarsOfBranches, hbs, hhead, List.mem_append] using hmem
            cases hmem' with
            | inl hcont =>
                have hfree : cont.isFreeIn v = true := mem_freeVars_isFreeIn cont v hcont
                simp [isFreeInBranches', hbs, hfree]
            | inr htail =>
                have hfree := mem_freeVarsOfBranches_isFreeInBranches' tail v htail
                simp [isFreeInBranches', hbs, hfree]
  termination_by sizeOf bs
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega
end

/-- Check if a variable is guarded (only appears inside send/recv) in a local type.
    A variable is guarded if it doesn't appear at the "head" position -
    i.e., only inside the continuations of communications, not at mu bodies before communications.

    This predicate checks if variable v is guarded at the current position:
    - In end: trivially true (no v)
    - In var w: must not be v (unguarded occurrence)
    - In send/recv: any occurrence in branches is guarded (inside comm)
    - In mu t body: if t = v, shadowed so ok; otherwise must check body -/
def LocalTypeR.isGuarded (v : String) : LocalTypeR → Bool
  | .end => true
  | .var w => v != w  -- v appears unguarded if this IS v
  | .send _ _ => true  -- Any occurrence of v in branches is guarded (inside comm)
  | .recv _ _ => true  -- Any occurrence of v in branches is guarded (inside comm)
  | .mu t body => if v == t then true else body.isGuarded v

mutual
  /-- A local type is contractive if every mu-bound variable is guarded in its body.
      This ensures mu-unfolding eventually reaches a communication. -/
  def LocalTypeR.isContractive : LocalTypeR → Bool
    | .end => true
    | .var _ => true
    | .send _ bs => isContractiveBranches bs
    | .recv _ bs => isContractiveBranches bs
    | .mu t body => body.isGuarded t && body.isContractive

  /-- Helper: check if all branches are contractive. -/
  def isContractiveBranches : List (Label × LocalTypeR) → Bool
    | [] => true
    | (_, c) :: rest => c.isContractive && isContractiveBranches rest
end


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
    | .send p bs => by
        simp [LocalTypeR.substitute, LocalTypeR.freeVars, -substituteBranches_eq_map] at hx
        exact freeVars_substituteBranches_subset_aux bs varName repl x hx
    | .recv p bs => by
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

/-! ## Full Unfolding (Coq-style `full_eunf`)

Iterate mu-unfolding until reaching a non-mu form.
This is the Coq pattern where predicates work on fully unfolded types. -/

/-- Height for mu unfolding - counts nested mus at the head. -/
def LocalTypeR.muHeight : LocalTypeR → Nat
  | .mu _ body => 1 + body.muHeight
  | _ => 0

/-- Fully unfold a local type by iterating unfold until non-mu form.
    Corresponds to Coq's `full_eunf`. -/
def LocalTypeR.fullUnfold (lt : LocalTypeR) : LocalTypeR :=
  (LocalTypeR.unfold)^[lt.muHeight] lt

/-- If a type has no leading `mu`, then `fullUnfold` cannot be a `mu`.

    This is the only unconditional statement we can make without assuming
    guardedness/contractiveness. -/
theorem LocalTypeR.fullUnfold_not_mu (lt : LocalTypeR) :
    lt.muHeight = 0 → ∀ t body, lt.fullUnfold ≠ .mu t body := by
  intro h t body
  cases lt <;> simp [fullUnfold, muHeight] at h ⊢

/-- fullUnfold is idempotent when its result has no leading `mu`. -/
theorem LocalTypeR.fullUnfold_idemp (lt : LocalTypeR) :
    lt.fullUnfold.muHeight = 0 → lt.fullUnfold.fullUnfold = lt.fullUnfold := by
  intro h
  have h' : ((LocalTypeR.unfold)^[lt.muHeight] lt).muHeight = 0 := by
    simpa [fullUnfold] using h
  simp [fullUnfold, h']


/-! ## Guardedness and muHeight Properties -/

/-- For non-mu types, unfold is identity. -/
theorem LocalTypeR.unfold_non_mu (lt : LocalTypeR) :
    (∀ t body, lt ≠ .mu t body) → lt.unfold = lt := by
  intro h
  match lt with
  | «end» | var _ | send _ _ | recv _ _ => rfl
  | .mu t body => exact absurd rfl (h t body)

/-- The result of unfold on a mu is the substituted body. -/
theorem LocalTypeR.unfold_mu (t : String) (body : LocalTypeR) :
    (.mu t body : LocalTypeR).unfold = body.substitute t (.mu t body) := rfl

/-- fullUnfold of mu unfolds via one step of unfold then iterate.

    This follows from the definition: fullUnfold (.mu t body) = unfold^[1 + body.muHeight] (.mu t body)
    and Function.iterate_succ_apply: f^[n+1] x = f^[n] (f x).

    Corresponds to Coq's `full_eunf_subst`. -/
theorem LocalTypeR.fullUnfold_mu (t : String) (body : LocalTypeR) :
    (.mu t body : LocalTypeR).fullUnfold =
      LocalTypeR.unfold^[body.muHeight] (body.substitute t (.mu t body)) := by
  -- fullUnfold (.mu t body) = unfold^[(.mu t body).muHeight] (.mu t body)
  --                         = unfold^[1 + body.muHeight] (.mu t body)
  --                         = unfold^[body.muHeight] (unfold (.mu t body))
  --                         = unfold^[body.muHeight] (body.substitute t (.mu t body))
  simp only [fullUnfold, muHeight]
  -- Goal: unfold^[1 + body.muHeight] (.mu t body) = unfold^[body.muHeight] (body.substitute ...)
  rw [Nat.add_comm, Function.iterate_succ_apply]
  -- Goal: unfold^[body.muHeight] (unfold (.mu t body)) = unfold^[body.muHeight] (body.substitute ...)
  rfl

/-! ## Key Property: Contractive types reach observable form

For closed, contractive types, fullUnfold always reaches a non-mu form.
This is because:
1. Contractive means all bound variables are guarded
2. Guarded variables only appear inside send/recv
3. So fullUnfold reaches send/recv/end (not var since closed) -/

/-- Classification of fully unfolded types. -/
inductive FullUnfoldResult where
  | is_end : FullUnfoldResult
  | is_var (v : String) : FullUnfoldResult
  | is_send (p : String) (bs : List (Label × LocalTypeR)) : FullUnfoldResult
  | is_recv (p : String) (bs : List (Label × LocalTypeR)) : FullUnfoldResult

/-- Classify the result of full unfolding a non-mu type. -/
def LocalTypeR.classifyNonMu : LocalTypeR → FullUnfoldResult
  | .end => .is_end
  | .var v => .is_var v
  | .send p bs => .is_send p bs
  | .recv p bs => .is_recv p bs
  | .mu _ _ => .is_end  -- Shouldn't be called on mu, but need total function

/-- For a type with muHeight 0 (non-mu at head), fullUnfold returns the type itself. -/
theorem LocalTypeR.fullUnfold_muHeight_zero {lt : LocalTypeR} (h : lt.muHeight = 0) :
    lt.fullUnfold = lt := by
  simp [fullUnfold, h]

/-- Non-mu types have muHeight 0. -/
theorem LocalTypeR.muHeight_non_mu :
    ∀ (lt : LocalTypeR), (∀ t body, lt ≠ .mu t body) → lt.muHeight = 0 := by
  intro lt h
  cases lt with
  | «end» => rfl
  | var _ => rfl
  | send _ _ => rfl
  | recv _ _ => rfl
  | mu t body => exact absurd rfl (h t body)

/- For closed types (no free variables), fullUnfold cannot produce a variable.

    This is a useful auxiliary lemma (though not strictly needed for observable_of_closed_contractive
    since we prove it directly by induction).

    Intuition:
    - Closed means freeVars = []
    - If fullUnfold = .var v, then v would be free in the original type
    - But closed types have no free variables, contradiction

    Proof sketch: By contrapositive of unguarded_unfolds_to_var.
    If fullUnfold = .var v, then by unguarded_unfolds_to_var, v is free and unguarded.
    But isClosed means no free variables, contradiction.

    Note: This doesn't require contractiveness! Closedness alone ensures fullUnfold ≠ .var. -/
-- Helper: isFreeIn v = true implies v ∈ freeVars
mutual
  theorem isFreeIn_mem_freeVars (lt : LocalTypeR) (v : String) :
      lt.isFreeIn v = true → v ∈ lt.freeVars := by
    intro h
    cases hlt : lt with
    | «end» =>
        simp [LocalTypeR.isFreeIn, LocalTypeR.freeVars, hlt] at h
    | var w =>
        have hv : v = w := by
          simpa [LocalTypeR.isFreeIn, beq_iff_eq, hlt] using h
        subst hv
        simp [LocalTypeR.freeVars, hlt]
    | send _ bs =>
        have h' : isFreeInBranches' v bs = true := by
          simpa [LocalTypeR.isFreeIn, hlt] using h
        have hmem := isFreeInBranches'_mem_freeVarsOfBranches bs v h'
        simpa [LocalTypeR.freeVars, hlt] using hmem
    | recv _ bs =>
        have h' : isFreeInBranches' v bs = true := by
          simpa [LocalTypeR.isFreeIn, hlt] using h
        have hmem := isFreeInBranches'_mem_freeVarsOfBranches bs v h'
        simpa [LocalTypeR.freeVars, hlt] using hmem
    | mu t body =>
        by_cases hvt : v = t
        · have hbeq : (v == t) = true := by
            simpa [beq_iff_eq] using hvt
          have hfalse : False := by
            simpa [LocalTypeR.isFreeIn, hbeq, hlt] using h
          exact False.elim hfalse
        · have hvne : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
          have h' : body.isFreeIn v = true := by
            simpa [LocalTypeR.isFreeIn, hvne, hlt] using h
          have hmem : v ∈ body.freeVars := isFreeIn_mem_freeVars body v h'
          apply (List.mem_filter).2
          exact ⟨hmem, (bne_iff_ne).2 hvt⟩
  termination_by sizeOf lt
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega

  theorem isFreeInBranches'_mem_freeVarsOfBranches (bs : List (Label × LocalTypeR)) (v : String) :
      isFreeInBranches' v bs = true → v ∈ freeVarsOfBranches bs := by
    intro h
    cases hbs : bs with
    | nil =>
        simp [isFreeInBranches', freeVarsOfBranches, hbs] at h
    | cons head tail =>
        cases hhead : head with
        | mk label cont =>
            have h' : cont.isFreeIn v = true ∨ isFreeInBranches' v tail = true := by
              simpa [isFreeInBranches', hbs, hhead, Bool.or_eq_true] using h
            cases h' with
            | inl hcont =>
                have hmem : v ∈ cont.freeVars := isFreeIn_mem_freeVars cont v hcont
                simp [freeVarsOfBranches, hbs, hmem]
            | inr htail =>
                have hmem := isFreeInBranches'_mem_freeVarsOfBranches tail v htail
                simp [freeVarsOfBranches, hbs, hmem]
  termination_by sizeOf bs
  decreasing_by
    classical
    all_goals
      simp [*] <;> omega
end

-- If v is not free in lt, then it is guarded in lt.
theorem isGuarded_of_isFreeIn_false (lt : LocalTypeR) (v : String) :
    lt.isFreeIn v = false → lt.isGuarded v = true := by
  intro h
  cases lt with
  | «end» =>
      simp [LocalTypeR.isGuarded]
  | var w =>
      have hv : v ≠ w := by
        have hbeq : (v == w) = false := by
          simpa [LocalTypeR.isFreeIn] using h
        exact (beq_eq_false_iff_ne).1 hbeq
      have hvb : (v != w) = true := (bne_iff_ne).2 hv
      simp [LocalTypeR.isGuarded, hvb]
  | send _ _ =>
      simp [LocalTypeR.isGuarded]
  | recv _ _ =>
      simp [LocalTypeR.isGuarded]
  | mu t body =>
      by_cases hvt : v = t
      · subst hvt
        simp [LocalTypeR.isGuarded]
      · have hvne : (v == t) = false := beq_eq_false_iff_ne.mpr hvt
        have hbody : body.isFreeIn v = false := by
          simpa [LocalTypeR.isFreeIn, hvne] using h
        have hbody' := isGuarded_of_isFreeIn_false body v hbody
        simp [LocalTypeR.isGuarded, hvne, hbody']
termination_by sizeOf lt

-- Closed types have all variables guarded.
theorem isGuarded_of_closed (lt : LocalTypeR) (v : String) :
    lt.isClosed → lt.isGuarded v = true := by
  intro hclosed
  cases hfree : lt.isFreeIn v with
  | true =>
      have hmem := isFreeIn_mem_freeVars lt v hfree
      have hnil : lt.freeVars = [] := by
        have : lt.freeVars.isEmpty = true := by
          simpa [LocalTypeR.isClosed] using hclosed
        exact (List.isEmpty_eq_true _).1 this
      have : False := by
        simpa [hnil] using hmem
      exact this.elim
  | false =>
      exact isGuarded_of_isFreeIn_false lt v hfree

/-! ## Closed Types and Substitution -/

theorem isFreeIn_false_of_closed (lt : LocalTypeR) (v : String) :
    lt.isClosed → lt.isFreeIn v = false := by
  intro hclosed
  cases hfree : lt.isFreeIn v with
  | true =>
      have hmem := isFreeIn_mem_freeVars lt v hfree
      have hnil : lt.freeVars = [] := by
        have : lt.freeVars.isEmpty = true := by
          simpa [LocalTypeR.isClosed] using hclosed
        exact (List.isEmpty_eq_true _).1 this
      have : False := by
        simpa [hnil] using hmem
      exact this.elim
  | false =>
      simpa using hfree

mutual
  theorem substitute_not_free (e : LocalTypeR) (x : String) (rx : LocalTypeR)
      (hnot_free : LocalTypeR.isFreeIn x e = false) :
      e.substitute x rx = e := by
    match e with
    | .end => rfl
    | .var w =>
        by_cases hwt : w = x
        · subst hwt
          have : False := by
            simpa [LocalTypeR.isFreeIn] using hnot_free
          exact this.elim
        · have hbeq : (w == x) = false := beq_eq_false_iff_ne.mpr hwt
          simp [LocalTypeR.substitute, hbeq]
    | .send p bs =>
        have hbs : isFreeInBranches' x bs = false := by
          simpa [LocalTypeR.isFreeIn] using hnot_free
        have hbs' := substituteBranches_not_free bs x rx hbs
        simpa [LocalTypeR.substitute, hbs', -substituteBranches_eq_map]
    | .recv p bs =>
        have hbs : isFreeInBranches' x bs = false := by
          simpa [LocalTypeR.isFreeIn] using hnot_free
        have hbs' := substituteBranches_not_free bs x rx hbs
        simpa [LocalTypeR.substitute, hbs', -substituteBranches_eq_map]
    | .mu t body =>
        by_cases hxt : t = x
        · have hbeq : (t == x) = true := by
            simpa [beq_iff_eq] using hxt
          simp [LocalTypeR.substitute, hbeq]
        · have hbeq : (t == x) = false := beq_eq_false_iff_ne.mpr hxt
          have hxt' : x ≠ t := by
            intro hx
            exact hxt hx.symm
          have hxtbeq : (x == t) = false := beq_eq_false_iff_ne.mpr hxt'
          have hbody : LocalTypeR.isFreeIn x body = false := by
            simpa [LocalTypeR.isFreeIn, hxtbeq] using hnot_free
          have hbody' := substitute_not_free body x rx hbody
          simp [LocalTypeR.substitute, hbeq, hbody']
  termination_by sizeOf e

  theorem substituteBranches_not_free (bs : List (Label × LocalTypeR)) (x : String) (rx : LocalTypeR)
      (hnot_free : isFreeInBranches' x bs = false) :
      LocalTypeR.substituteBranches bs x rx = bs := by
    match bs with
    | [] => rfl
    | (label, cont) :: rest =>
        have hsplit : cont.isFreeIn x = false ∧ isFreeInBranches' x rest = false := by
          simpa [isFreeInBranches', Bool.or_eq_false_iff] using hnot_free
        have h1 : cont.substitute x rx = cont :=
          substitute_not_free cont x rx hsplit.1
        have h2 : LocalTypeR.substituteBranches rest x rx = rest :=
          substituteBranches_not_free rest x rx hsplit.2
        simp [LocalTypeR.substituteBranches, h1, h2, -substituteBranches_eq_map]
  termination_by sizeOf bs
end

theorem apply_env_of_closed (env : Env) (lt : LocalTypeR) :
    lt.isClosed → Env.apply env lt = lt := by
  intro hclosed
  induction env generalizing lt with
  | nil =>
      simp [Env.apply]
  | cons head rest ih =>
      cases head with
      | mk v u =>
          have hnot : lt.isFreeIn v = false := isFreeIn_false_of_closed lt v hclosed
          have hsubst : lt.substitute v u = lt := substitute_not_free lt v u hnot
          have ih' := ih (lt := lt) hclosed
          simpa [Env.apply, hsubst] using ih'

theorem applyActiveEnv_eq_of_closed (lt : LocalTypeR) :
    lt.isClosed → applyActiveEnv lt = lt := by
  intro hclosed
  simpa [applyActiveEnv] using apply_env_of_closed ActiveEnv lt hclosed

-- Helper: if fullUnfold = .var v, then isFreeIn v = true
theorem fullUnfold_var_is_free (lt : LocalTypeR) (v : String) :
    lt.fullUnfold = .var v → lt.isFreeIn v = true := by
  intro h
  -- v is free in fullUnfold, so v is free in lt by iterated unfold subset
  have hv_mem_full : v ∈ lt.fullUnfold.freeVars := by
    -- fullUnfold = var v, whose freeVars is [v]
    simpa [h, LocalTypeR.freeVars] using (List.mem_cons_self v [])
  have hv_mem : v ∈ lt.freeVars := by
    have hsubset := freeVars_iter_unfold_subset (k := lt.muHeight) (lt := lt) (v := v) hv_mem_full
    simpa [LocalTypeR.fullUnfold] using hsubset
  exact mem_freeVars_isFreeIn lt v hv_mem

theorem LocalTypeR.fullUnfold_not_var_of_closed {lt : LocalTypeR}
    (hclosed : lt.isClosed) : ∀ v, lt.fullUnfold ≠ .var v := by
  intro v h
  have hfree : lt.isFreeIn v = true := fullUnfold_var_is_free lt v h
  have hmem : v ∈ lt.freeVars := isFreeIn_mem_freeVars lt v hfree
  have hnil : lt.freeVars = [] := by
    have : lt.freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have : False := by
    simpa [hnil] using hmem
  exact this.elim

/-- For contractive types, fullUnfold reaches a non-mu form.

    Contractiveness ensures that after muHeight iterations of unfold,
    we reach a communication (send/recv) or end, not another mu.

    This follows from the definition: fullUnfold iterates unfold exactly
    muHeight times, which peels off all leading mus for contractive types. -/
-- Helper from LocalTypeCore - muHeight of guarded substitution
theorem muHeight_substitute_guarded (t : String) (body e : LocalTypeR) :
    body.isGuarded t = true → (body.substitute t e).muHeight ≤ body.muHeight := by
  intro hguard
  cases body with
  | «end» =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | var w =>
      by_cases hw : w = t
      · subst hw
        have : False := by
          simpa [LocalTypeR.isGuarded] using hguard
        exact this.elim
      · have hbeq : (w == t) = false := beq_eq_false_iff_ne.mpr hw
        simp [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq]
  | send p bs =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | recv p bs =>
      simp [LocalTypeR.substitute, LocalTypeR.muHeight]
  | mu s body =>
      by_cases hs : s = t
      · have hbeq : (s == t) = true := by
          simpa [beq_iff_eq] using hs
        -- Shadowed: no substitution under mu
        simp [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq]
      · have hbeq_st : (s == t) = false := beq_eq_false_iff_ne.mpr hs
        have hbeq_ts : (t == s) = false := beq_eq_false_iff_ne.mpr (by intro h; exact hs h.symm)
        -- Substitute under mu; use recursion on body
        have hguard' : body.isGuarded t = true := by
          simpa [LocalTypeR.isGuarded, hbeq_ts] using hguard
        have ih := muHeight_substitute_guarded t body e hguard'
        have := Nat.add_le_add_left ih 1
        simpa [LocalTypeR.substitute, LocalTypeR.muHeight, hbeq_st] using this
termination_by sizeOf body

-- Helper: isGuarded is preserved by substitution when replacing with closed term
theorem isGuarded_substitute (body : LocalTypeR) (t v : String) (e : LocalTypeR) :
    body.isGuarded v = true → e.isClosed →
    (body.substitute t e).isGuarded v = true := by
  intro hguard hclosed
  cases body with
  | «end» =>
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
  | var w =>
      by_cases hw : w = t
      · subst hw
        have hguard_e : e.isGuarded v = true := isGuarded_of_closed e v hclosed
        simpa [LocalTypeR.substitute] using hguard_e
      · have hbeq : (w == t) = false := beq_eq_false_iff_ne.mpr hw
        simpa [LocalTypeR.substitute, LocalTypeR.isGuarded, hbeq] using hguard
  | send _ _ | recv _ _ =>
      -- Send and recv cases are identical (symmetric under duality)
      simp [LocalTypeR.substitute, LocalTypeR.isGuarded]
  | mu s body =>
      by_cases hs : s = t
      · have hbeq : (s == t) = true := by
          simpa [beq_iff_eq] using hs
        simpa [LocalTypeR.substitute, hbeq] using hguard
      · have hbeq_st : (s == t) = false := beq_eq_false_iff_ne.mpr hs
        by_cases hvs : v = s
        · subst hvs
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hbeq_st]
        · have hvbeq : (v == s) = false := beq_eq_false_iff_ne.mpr hvs
          have hguard' : body.isGuarded v = true := by
            simpa [LocalTypeR.isGuarded, hvbeq] using hguard
          have ih := isGuarded_substitute body t v e hguard' hclosed
          simp [LocalTypeR.substitute, LocalTypeR.isGuarded, hbeq_st, hvbeq, ih]
termination_by sizeOf body

-- Helper: isGuarded is preserved by substitution for variables OTHER than the substituted one
-- Requires closed replacement to avoid introducing unguarded occurrences.
theorem isGuarded_substitute_other (body : LocalTypeR) (t v : String) (e : LocalTypeR) :
    v ≠ t → body.isGuarded v = true →
    e.isClosed → (body.substitute t e).isGuarded v = true := by
  intro _ hguard hclosed
  exact isGuarded_substitute body t v e hguard hclosed

-- NOTE: isContractive_substitute_mu is proved in LocalTypeRDBBridge.lean

-- Helper: substitution preserves contractiveness when replacing with contractive, closed term
-- Note: The mu case requires closedness to avoid introducing unguarded variables.
mutual
  theorem isContractive_substitute (body : LocalTypeR) (t : String) (e : LocalTypeR) :
      body.isContractive = true → e.isContractive = true → e.isClosed →
      (body.substitute t e).isContractive = true := by
    intro hbody hcontr hclosed
    cases body with
    | «end» =>
        simp [LocalTypeR.substitute, LocalTypeR.isContractive]
    | var w =>
        by_cases hw : w = t
        · subst hw
          simpa [LocalTypeR.substitute] using hcontr
        · have hbeq : (w == t) = false := beq_eq_false_iff_ne.mpr hw
          simp [LocalTypeR.substitute, LocalTypeR.isContractive, hbeq]
    | send p bs | recv p bs =>
        -- Send and recv cases are identical (symmetric under duality)
        have hbs : isContractiveBranches bs = true := by
          simpa [LocalTypeR.isContractive] using hbody
        have hbs' : isContractiveBranches (substituteBranches bs t e) = true :=
          isContractiveBranches_substitute bs t e hbs hcontr hclosed
        simp [LocalTypeR.substitute, LocalTypeR.isContractive, hbs', -substituteBranches_eq_map]
    | mu s body =>
        by_cases hs : s = t
        · have hbeq : (s == t) = true := by
            simpa [beq_iff_eq] using hs
          simpa [LocalTypeR.substitute, LocalTypeR.isContractive, hbeq] using hbody
        · have hbeq : (s == t) = false := beq_eq_false_iff_ne.mpr hs
          have hpair : body.isGuarded s = true ∧ body.isContractive = true := by
            simpa [LocalTypeR.isContractive, Bool.and_eq_true] using hbody
          have hguard : body.isGuarded s = true := hpair.1
          have hbody_contr : body.isContractive = true := hpair.2
          have hguard' : (body.substitute t e).isGuarded s = true :=
            isGuarded_substitute body t s e hguard hclosed
          have hbody' : (body.substitute t e).isContractive = true :=
            isContractive_substitute body t e hbody_contr hcontr hclosed
          simp [LocalTypeR.substitute, LocalTypeR.isContractive, hbeq, hguard', hbody']
  termination_by sizeOf body

  theorem isContractiveBranches_substitute (bs : List (Label × LocalTypeR)) (t : String) (e : LocalTypeR) :
      isContractiveBranches bs = true → e.isContractive = true → e.isClosed →
      isContractiveBranches (substituteBranches bs t e) = true := by
    intro hbs hcontr hclosed
    cases bs with
    | nil =>
        simp [isContractiveBranches]
    | cons head tail =>
        cases head with
        | mk label cont =>
            have hpair : cont.isContractive = true ∧ isContractiveBranches tail = true := by
              simpa [isContractiveBranches, Bool.and_eq_true] using hbs
            have hcont' : (cont.substitute t e).isContractive = true :=
              isContractive_substitute cont t e hpair.1 hcontr hclosed
            have htail' : isContractiveBranches (substituteBranches tail t e) = true :=
              isContractiveBranches_substitute tail t e hpair.2 hcontr hclosed
            simp [isContractiveBranches, LocalTypeR.substituteBranches, hcont', htail', -substituteBranches_eq_map]
  termination_by sizeOf bs
end

-- Helper: iterating unfold k times on CLOSED, CONTRACTIVE term with muHeight ≤ k yields muHeight 0
/-! ## ClosedUnder through substitution/apply -/

theorem LocalTypeR.isClosed_substitute_mu {t : String} {body : LocalTypeR}
    (hclosed : (LocalTypeR.mu t body).isClosed) :
    (body.substitute t (LocalTypeR.mu t body)).isClosed := by
  -- Convert isClosed to freeVars = []
  have hmu_nil : (LocalTypeR.mu t body).freeVars = [] := by
    have : (LocalTypeR.mu t body).freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have hfilter_nil : body.freeVars.filter (· != t) = [] := by
    simpa [LocalTypeR.freeVars] using hmu_nil
  -- Show substituted freeVars is empty
  simp [LocalTypeR.isClosed, List.isEmpty_eq_true, List.eq_nil_iff_forall_not_mem]
  intro v hv
  have hres := freeVars_substitute_closed body t (.mu t body) hclosed v hv
  have hmem_filter : v ∈ body.freeVars.filter (· != t) := by
    apply List.mem_filter.mpr
    exact ⟨hres.1, (bne_iff_ne).2 hres.2⟩
  -- Contradiction with hfilter_nil
  simpa [hfilter_nil] using hmem_filter

theorem closedUnder_substitute_closed {env : Env} {t : LocalTypeR}
    (v : String) (u : LocalTypeR) :
    u.isClosed → ClosedUnder ((v, u) :: env) t → ClosedUnder env (t.substitute v u) := by
  intro hclosed hcu x hx
  have hres := freeVars_substitute_closed t v u hclosed x hx
  have hx_in : x ∈ t.freeVars := hres.1
  have hxne : x ≠ v := hres.2
  have hx_dom : x ∈ Env.dom ((v, u) :: env) := hcu x hx_in
  have hx_dom' : x = v ∨ x ∈ Env.dom env := by
    simpa [Env.dom] using (List.mem_cons.mp hx_dom)
  cases hx_dom' with
  | inl hx_eq => exact (hxne hx_eq).elim
  | inr hx_rest => exact hx_rest

theorem isClosed_apply_of_closed_env (env : Env) (t : LocalTypeR) :
    EnvWellFormed env → ClosedUnder env t → (Env.apply env t).isClosed := by
  intro hWF hclosed
  induction env generalizing t with
  | nil =>
      have hclosed' : t.isClosed := (closedUnder_nil_iff_isClosed t).1 hclosed
      simpa [Env.apply] using hclosed'
  | cons head rest ih =>
      cases head with
      | mk v u =>
          rcases hWF with ⟨hu_closed, _hu_contr, hWF_rest⟩
          have hclosed_subst : ClosedUnder rest (t.substitute v u) :=
            closedUnder_substitute_closed (env := rest) (t := t) v u hu_closed hclosed
          have hclosed_apply := ih (t := t.substitute v u) hWF_rest hclosed_subst
          simpa [Env.apply] using hclosed_apply

theorem isContractive_apply_of_closed_env (env : Env) (t : LocalTypeR) :
    EnvWellFormed env → t.isContractive = true → (Env.apply env t).isContractive = true := by
  intro hWF hcontr
  induction env generalizing t with
  | nil =>
      simpa [Env.apply] using hcontr
  | cons head rest ih =>
      cases head with
      | mk v u =>
          rcases hWF with ⟨hu_closed, hu_contr, hWF_rest⟩
          have hcontr_subst : (t.substitute v u).isContractive = true :=
            isContractive_substitute t v u hcontr hu_contr hu_closed
          have hcontr_apply := ih (t := t.substitute v u) hWF_rest hcontr_subst
          simpa [Env.apply] using hcontr_apply

theorem iterate_unfold_bounded_contractive (k : Nat) (e : LocalTypeR)
    (hcontr : e.isContractive = true) (hclosed : e.isClosed) (h : e.muHeight ≤ k) :
    ((LocalTypeR.unfold)^[k] e).muHeight = 0 := by
  induction k generalizing e with
  | zero =>
      have hmh : e.muHeight = 0 := Nat.le_zero.mp h
      simp [Function.iterate_zero, hmh]
  | succ k ih =>
      cases e with
      | «end» =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.end) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | var w =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.var w) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | send p bs =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.send p bs) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | recv p bs =>
          have hiter := Function.iterate_fixed (f := LocalTypeR.unfold) (x := LocalTypeR.recv p bs) rfl (n := Nat.succ k)
          simpa [LocalTypeR.muHeight] using congrArg LocalTypeR.muHeight hiter
      | mu t body =>
          -- Extract guardness and contractiveness of body
          have hpair : body.isGuarded t = true ∧ body.isContractive = true := by
            simpa [LocalTypeR.isContractive, Bool.and_eq_true] using hcontr
          have hguarded : body.isGuarded t = true := hpair.1
          have hbody_contr : body.isContractive = true := hpair.2
          have hle : body.muHeight ≤ k := by
            -- muHeight (.mu t body) = 1 + body.muHeight
            have h' : 1 + body.muHeight ≤ 1 + k := by
              simpa [LocalTypeR.muHeight, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
            exact Nat.le_of_add_le_add_left h'
          -- Substitution preserves contractiveness (needed for IH)
          have hsubst_contr : (body.substitute t (.mu t body)).isContractive = true :=
            isContractive_substitute body t (.mu t body) hbody_contr hcontr hclosed
          have hsubst_closed : (body.substitute t (.mu t body)).isClosed :=
            LocalTypeR.isClosed_substitute_mu hclosed
          -- Mu-height does not increase under guarded substitution
          have hsubst_h : (body.substitute t (.mu t body)).muHeight ≤ k := by
            have hle' : (body.substitute t (.mu t body)).muHeight ≤ body.muHeight :=
              muHeight_substitute_guarded t body (.mu t body) hguarded
            exact le_trans hle' hle
          have ih' := ih (e := body.substitute t (.mu t body)) hsubst_contr hsubst_closed hsubst_h
          -- unfold^[k+1] (.mu t body) = unfold^[k] (body.substitute t (.mu t body))
          simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih'

theorem LocalTypeR.fullUnfold_non_mu_of_contractive {lt : LocalTypeR}
    (hcontr : lt.isContractive = true) (hclosed : lt.isClosed) : lt.fullUnfold.muHeight = 0 := by
  simp [fullUnfold]
  apply iterate_unfold_bounded_contractive
  · exact hcontr
  · exact hclosed
  · simp

/-! ## Unguarded Variable Theorem (Coq's `eguarded_test`)

This is the key bridge between guardedness and observable behavior.
If a variable is free in a type but NOT guarded, then the type fully
unfolds to that variable.

The intuition is:
- An unguarded free variable sits at the "head" position
- Unfolding only substitutes under mu, so the variable stays at head
- After enough unfolding, we reach just the variable -/

/-- Helper for double substitution case in unfold_iter_subst_unguarded.

    NOTE: This theorem is NOT NEEDED for the contractive case!

    For closed + contractive types, fullUnfold can never reach .var because:
    1. Closed means no free variables → no unbound vars
    2. Contractive means all bound variables are guarded → no bound vars at head after unfolding

    This complex double substitution theorem only matters for NON-contractive types
    with unguarded variables, which are not our target use case.

    The theorem statement is now restricted to closed bodies, where it is vacuous,
    and kept only for API completeness. -/
theorem LocalTypeR.unfold_iter_double_subst (body : LocalTypeR)
    (t : String) (repl : LocalTypeR) (s : String) (v : String)
    (hvt : v ≠ t) (hvs : v ≠ s)
    (hclosed : body.isClosed)
    (h_free : body.isFreeIn v = true) (h_not_guarded : body.isGuarded v = false) :
    (LocalTypeR.unfold)^[body.muHeight] ((body.substitute t repl).substitute s (.mu s (body.substitute t repl))) = .var v := by
  -- For closed bodies this is vacuous: no free variables exist.
  have hmem : v ∈ body.freeVars := isFreeIn_mem_freeVars body v h_free
  have hnil : body.freeVars = [] := by
    have : body.freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have : False := by
    simpa [hnil] using hmem
  exact this.elim

/-- Auxiliary lemma for unguarded_unfolds_to_var.

    If v is free and unguarded in e, and v ≠ t, then iterating unfold e.muHeight
    times on (e.substitute t repl) gives .var v.

    This is the generalization of Coq's `eguarded_test` that handles arbitrary substitutions.
    The key insight is that the iteration count is determined by the ORIGINAL type e,
    not by the substituted type. Since v ≠ t, substituting t doesn't affect occurrences of v,
    and after e.muHeight iterations, we reach .var v.

    This lemma is now restricted to closed types, where it is vacuous. -/
theorem LocalTypeR.unfold_iter_subst_unguarded (e : LocalTypeR) (t : String) (repl : LocalTypeR)
    (v : String) (hvt : v ≠ t)
    (hclosed : e.isClosed)
    (h_free : e.isFreeIn v = true) (h_not_guarded : e.isGuarded v = false) :
    (LocalTypeR.unfold)^[e.muHeight] (e.substitute t repl) = .var v := by
  -- For closed types this is vacuous: no free variables exist.
  have hmem : v ∈ e.freeVars := isFreeIn_mem_freeVars e v h_free
  have hnil : e.freeVars = [] := by
    have : e.freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have : False := by
    simpa [hnil] using hmem
  exact this.elim

/-- If a variable is not guarded in a type (appears at head position after unfolding),
    then fully unfolding produces that variable.

    This corresponds to Coq's `eguarded_test`:
    ```coq
    Lemma eguarded_test : forall e sigma i, ~~ eguarded i e ->
      iter (emu_height e) eunf e [e sigma] = sigma i.
    ```

    This lemma is now restricted to closed types, where it is vacuous. -/
theorem LocalTypeR.unguarded_unfolds_to_var (lt : LocalTypeR) (v : String)
    (hclosed : lt.isClosed)
    (h_free : lt.isFreeIn v = true) (h_not_guarded : lt.isGuarded v = false) :
    lt.fullUnfold = .var v := by
  -- For closed types this is vacuous: no free variables exist.
  have hmem : v ∈ lt.freeVars := isFreeIn_mem_freeVars lt v h_free
  have hnil : lt.freeVars = [] := by
    have : lt.freeVars.isEmpty = true := by
      simpa [LocalTypeR.isClosed] using hclosed
    exact (List.isEmpty_eq_true _).1 this
  have : False := by
    simpa [hnil] using hmem
  exact this.elim

/-- The converse: if a free variable IS guarded, fullUnfold reaches a non-variable form.

    This is the key property for proving observable_of_closed: closed types
    (with all bound variables guarded) unfold to send/recv/end. -/
theorem LocalTypeR.guarded_fullUnfold_not_var (lt : LocalTypeR) (v : String)
    (h_guarded : lt.isGuarded v = true) (hclosed : lt.isClosed) :
    ∀ w, lt.fullUnfold ≠ .var w ∨ lt.isFreeIn v = false := by
  intro w
  right
  by_cases h_free : lt.isFreeIn v = true
  · have hmem : v ∈ lt.freeVars := isFreeIn_mem_freeVars lt v h_free
    have hnil : lt.freeVars = [] := by
      have : lt.freeVars.isEmpty = true := by
        simpa [LocalTypeR.isClosed] using hclosed
      exact (List.isEmpty_eq_true _).1 this
    have : False := by
      simpa [hnil] using hmem
    exact this.elim
  · simp [Bool.not_eq_true] at h_free
    exact h_free

end RumpsteakV2.Protocol.LocalTypeR
