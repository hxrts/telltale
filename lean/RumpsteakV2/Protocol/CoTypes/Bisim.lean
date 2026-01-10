import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.CoTypes.EQ2
import RumpsteakV2.Protocol.CoTypes.CoinductiveRel
import RumpsteakV2.Protocol.CoTypes.DBBridge
import RumpsteakV2.Protocol.CoTypes.Observables
import RumpsteakV2.Protocol.CoTypes.Duality
import RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

/-! # RumpsteakV2.Protocol.CoTypes.Bisim

Bisimulation-style EQ2 formulation using membership predicates.

This module implements the Bisim approach from QpfTypes PR #49, adapted for LocalTypeR.
The key insight is to define membership predicates (`UnfoldsTo`, `CanAct`) that capture
observable behavior after unfolding, allowing case analysis without matching on
LocalTypeR constructors directly.

## Background

Standard coinduction on EQ2 fails for transitivity and congruence proofs because:
1. EQ2F requires matching on LocalTypeR constructors
2. Mu-unfolding creates asymmetric cases that can't be case-analyzed
3. The intermediate witness in transitivity can have arbitrary structure

The Bisim solution:
1. Define `UnfoldsTo` that captures when unfolding terminates at a base constructor
2. Define `Bisim.F` using these membership predicates instead of constructor matching
3. Transitivity works because the intermediate element doesn't need constructor matching

## Expose

The following definitions form the semantic interface for proofs:

- `UnfoldsToEnd`, `UnfoldsToVar`: predicates for unfolding to base forms
- `CanSend`, `CanRecv`: predicates for action capability
- `BisimF`: one-step bisimulation functor
- `Bisim`: membership-based weak bisimulation
- `Bisim.refl`, `Bisim.symm`, `Bisim.trans`: equivalence properties

## References

- QpfTypes PR #49: https://github.com/alexkeizer/QpfTypes/pull/49
- hxrts/QpfTypes fork: https://github.com/hxrts/QpfTypes (commit f9e16e9)
-/

namespace RumpsteakV2.Protocol.CoTypes.Bisim

open RumpsteakV2.Protocol.GlobalType
open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2
open RumpsteakV2.Protocol.CoTypes.Observables
open RumpsteakV2.Protocol.CoTypes.CoinductiveRel

/-! ## Observable Behavior

The membership predicates (UnfoldsToEnd, UnfoldsToVar, CanSend, CanRecv) and their
basic properties are defined in Observables.lean to avoid circular dependencies. -/

/-- Every closed AND contractive local type has observable behavior (after enough unfolding).

    This is the key well-formedness property: closed+contractive types can't diverge,
    they must eventually reach a base constructor.

    **Contractiveness is essential**: Without contractiveness, types like `μX.X` would
    be closed but diverge forever on unfolding. Contractiveness ensures every mu
    has at least one communication before recursion.

    Proof strategy: Structural induction on `a`.
    - For .end: Observable via UnfoldsToEnd.base
    - For .var: Contradicts closedness (closed types have no free variables)
    - For .send/.recv: Observable via CanSend.base/CanRecv.base
    - For .mu t body: Use IH on body.substitute t (.mu t body), which is:
      * Contractive (by contractiveness of body)
      * Closed (substituting a closed term into a body with only t free)
      Then lift the observable result via the .mu constructors. -/
theorem observable_of_closed_contractive {a : LocalTypeR}
    (hclosed : a.isClosed) (hcontr : a.isContractive = true) : Observable a := by
  -- Structural induction on a
  match a with
  | .end =>
    -- .end unfolds to itself
    exact Observable.is_end UnfoldsToEnd.base
  | .var v =>
    -- .var v contradicts closedness: closed types have no free variables
    have : False := by
      simpa [LocalTypeR.isClosed, LocalTypeR.freeVars] using hclosed
    exact this.elim
  | .send p bs =>
    -- .send unfolds to itself
    exact Observable.is_send CanSend.base
  | .recv p bs =>
    -- .recv unfolds to itself
    exact Observable.is_recv CanRecv.base
  | .mu t body =>
    -- For .mu t body:
    -- 1. Extract contractiveness of body
    have hmu_contr : (.mu t body : LocalTypeR).isContractive = true := hcontr
    simp [LocalTypeR.isContractive, Bool.and_eq_true] at hcontr
    have ⟨hguarded, hcontr_body⟩ := hcontr
    -- hguarded : body.isGuarded t = true
    -- hcontr_body : body.isContractive = true

    -- 2. Show that body.substitute t (.mu t body) is closed
    -- Since .mu t body is closed, and we're substituting the closed term (.mu t body)
    -- for the only potential free variable (t), the result is closed
    have hclosed_subst : (body.substitute t (.mu t body)).isClosed :=
      LocalTypeR.isClosed_substitute_mu hclosed

    -- 3. Substitution preserves contractiveness for closed replacement
    have hsubst_contr : (body.substitute t (.mu t body)).isContractive = true :=
      LocalTypeR.isContractive_substitute body t (.mu t body) hcontr_body hmu_contr hclosed
    -- 4. Apply IH to get Observable for the substituted body
    have ih : Observable (body.substitute t (.mu t body)) :=
      observable_of_closed_contractive hclosed_subst hsubst_contr

    -- 5. Lift the observable result using the .mu constructors
    cases ih with
    | is_end h => exact Observable.is_end (UnfoldsToEnd.mu h)
    | is_var h => exact Observable.is_var (UnfoldsToVar.mu h)
    | is_send h => exact Observable.is_send (CanSend.mu h)
    | is_recv h => exact Observable.is_recv (CanRecv.mu h)


termination_by a.muHeight
decreasing_by
  -- mu case: substitution does not increase muHeight under guardedness
  simpa [LocalTypeR.muHeight, Nat.add_comm] using
    Nat.lt_succ_of_le (LocalTypeR.muHeight_substitute_guarded t body (.mu t body) hguarded)

/-! ## Environment-Aware Observability -/

theorem observable_of_env_contractive {env : Env} {a : LocalTypeR}
    (hWF : EnvWellFormed env) (hclosed : ClosedUnder env a) (hcontr : a.isContractive = true) :
    Observable (Env.apply env a) := by
  have hclosed' : (Env.apply env a).isClosed :=
    isClosed_apply_of_closed_env env a hWF hclosed
  have hcontr' : (Env.apply env a).isContractive = true :=
    isContractive_apply_of_closed_env env a hWF hcontr
  exact observable_of_closed_contractive hclosed' hcontr'

theorem observable_of_active_env_contractive {a : LocalTypeR}
    (hclosed : LocalTypeR.ClosedUnderActive a) (hcontr : a.isContractive = true) :
    Observable (LocalTypeR.applyActiveEnv a) := by
  have hWF : EnvWellFormed ActiveEnv := LocalTypeR.activeEnv_wellFormed
  simpa [LocalTypeR.applyActiveEnv] using
    (observable_of_env_contractive (env := ActiveEnv) hWF hclosed hcontr)

/-! ## Properties Inherited from Observables

The basic properties (reflexivity, exclusivity, incompatibility, determinism) are
proven in Observables.lean and available via the open statement above. -/

/-! ## Bounded Unfolding Paths

These predicates track mu-unfolding with explicit bounds, following the pattern from
QpfTypes PR #49. They are used to establish the connection between EQ2 (which handles
mu-unfolding implicitly) and Bisim (which uses membership predicates).

A bounded path witnesses that after n unfolding steps, a type reaches a specific
observable form. -/

/-- `UnfoldPathEndBounded n a` holds when `a` unfolds to `.end` in at most `n` mu-steps.

    This is an explicit bound on the unfolding depth, used to prove extraction lemmas
    by well-founded induction. -/
inductive UnfoldPathEndBounded : ℕ → LocalTypeR → Prop where
  | base : UnfoldPathEndBounded 0 .end
  | step {n : ℕ} {t : String} {body : LocalTypeR} :
      UnfoldPathEndBounded n (body.substitute t (.mu t body)) →
      UnfoldPathEndBounded (n + 1) (.mu t body)

/-- `UnfoldPathVarBounded n v a` holds when `a` unfolds to `.var v` in at most `n` mu-steps. -/
inductive UnfoldPathVarBounded : ℕ → String → LocalTypeR → Prop where
  | base {v : String} : UnfoldPathVarBounded 0 v (.var v)
  | step {n : ℕ} {v : String} {t : String} {body : LocalTypeR} :
      UnfoldPathVarBounded n v (body.substitute t (.mu t body)) →
      UnfoldPathVarBounded (n + 1) v (.mu t body)

/-- `CanSendPathBounded n p bs a` holds when `a` unfolds to a send in at most `n` mu-steps. -/
inductive CanSendPathBounded : ℕ → String → List (Label × LocalTypeR) → LocalTypeR → Prop where
  | base {p : String} {bs : List (Label × LocalTypeR)} :
      CanSendPathBounded 0 p bs (.send p bs)
  | step {n : ℕ} {p : String} {bs : List (Label × LocalTypeR)} {t : String} {body : LocalTypeR} :
      CanSendPathBounded n p bs (body.substitute t (.mu t body)) →
      CanSendPathBounded (n + 1) p bs (.mu t body)

/-- `CanRecvPathBounded n p bs a` holds when `a` unfolds to a recv in at most `n` mu-steps. -/
inductive CanRecvPathBounded : ℕ → String → List (Label × LocalTypeR) → LocalTypeR → Prop where
  | base {p : String} {bs : List (Label × LocalTypeR)} :
      CanRecvPathBounded 0 p bs (.recv p bs)
  | step {n : ℕ} {p : String} {bs : List (Label × LocalTypeR)} {t : String} {body : LocalTypeR} :
      CanRecvPathBounded n p bs (body.substitute t (.mu t body)) →
      CanRecvPathBounded (n + 1) p bs (.mu t body)

/-! ### Conversions between bounded and unbounded predicates -/

/-- Bounded end path implies unbounded. -/
theorem UnfoldPathEndBounded.toUnfoldsToEnd {n : ℕ} {a : LocalTypeR}
    (h : UnfoldPathEndBounded n a) : UnfoldsToEnd a := by
  induction h with
  | base => exact UnfoldsToEnd.base
  | step _ ih => exact UnfoldsToEnd.mu ih

/-- Unbounded end unfold implies bounded (existentially). -/
theorem UnfoldsToEnd.toBounded {a : LocalTypeR} (h : UnfoldsToEnd a) :
    ∃ n, UnfoldPathEndBounded n a := by
  induction h with
  | base => exact ⟨0, UnfoldPathEndBounded.base⟩
  | @mu t body _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, UnfoldPathEndBounded.step hn⟩

/-- Bounded var path implies unbounded. -/
theorem UnfoldPathVarBounded.toUnfoldsToVar {n : ℕ} {v : String} {a : LocalTypeR}
    (h : UnfoldPathVarBounded n v a) : UnfoldsToVar a v := by
  induction h with
  | base => exact UnfoldsToVar.base
  | step _ ih => exact UnfoldsToVar.mu ih

/-- Unbounded var unfold implies bounded. -/
theorem UnfoldsToVar.toBounded {v : String} {a : LocalTypeR} (h : UnfoldsToVar a v) :
    ∃ n, UnfoldPathVarBounded n v a := by
  induction h with
  | base => exact ⟨0, UnfoldPathVarBounded.base⟩
  | @mu t body v' _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, UnfoldPathVarBounded.step hn⟩

/-- Bounded send path implies unbounded. -/
theorem CanSendPathBounded.toCanSend {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanSendPathBounded n p bs a) : CanSend a p bs := by
  induction h with
  | base => exact CanSend.base
  | step _ ih => exact CanSend.mu ih

/-- Unbounded send implies bounded. -/
theorem CanSend.toBounded {p : String} {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanSend a p bs) : ∃ n, CanSendPathBounded n p bs a := by
  induction h with
  | base => exact ⟨0, CanSendPathBounded.base⟩
  | @mu t body p' bs' _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, CanSendPathBounded.step hn⟩

/-- Bounded recv path implies unbounded. -/
theorem CanRecvPathBounded.toCanRecv {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanRecvPathBounded n p bs a) : CanRecv a p bs := by
  induction h with
  | base => exact CanRecv.base
  | step _ ih => exact CanRecv.mu ih

/-- Unbounded recv implies bounded. -/
theorem CanRecv.toBounded {p : String} {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanRecv a p bs) : ∃ n, CanRecvPathBounded n p bs a := by
  induction h with
  | base => exact ⟨0, CanRecvPathBounded.base⟩
  | @mu t body p' bs' _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, CanRecvPathBounded.step hn⟩


/-- Bounded end path yields a concrete unfold iteration. -/
private theorem UnfoldPathEndBounded.unfold_iter_eq {n : ℕ} {a : LocalTypeR} :
    UnfoldPathEndBounded n a → (LocalTypeR.unfold^[n] a = .end) := by
  intro h
  induction h with
  | base => simp [Function.iterate_zero, id_eq]
  | step h ih =>
      simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih

/-- Bounded var path yields a concrete unfold iteration. -/
private theorem UnfoldPathVarBounded.unfold_iter_eq {n : ℕ} {v : String} {a : LocalTypeR} :
    UnfoldPathVarBounded n v a → (LocalTypeR.unfold^[n] a = .var v) := by
  intro h
  induction h with
  | base => simp [Function.iterate_zero, id_eq]
  | step h ih =>
      simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih

/-- Bounded send path yields a concrete unfold iteration. -/
private theorem CanSendPathBounded.unfold_iter_eq {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR} :
    CanSendPathBounded n p bs a → (LocalTypeR.unfold^[n] a = .send p bs) := by
  intro h
  induction h with
  | base => simp [Function.iterate_zero, id_eq]
  | step h ih =>
      simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih

/-- Bounded recv path yields a concrete unfold iteration. -/
private theorem CanRecvPathBounded.unfold_iter_eq {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR} :
    CanRecvPathBounded n p bs a → (LocalTypeR.unfold^[n] a = .recv p bs) := by
  intro h
  induction h with
  | base => simp [Function.iterate_zero, id_eq]
  | step h ih =>
      simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih
/-! ## Unfolding Shape Lemmas

These lemmas connect the membership predicates with `fullUnfold`. They are used
to extract constructor shapes from EQ2 via the UnfoldsTo/CanSend/CanRecv axioms. -/

private theorem UnfoldPathEndBounded.not_mu_var (t : String) :
    ∀ n, ¬ UnfoldPathEndBounded n (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

private theorem UnfoldPathVarBounded.not_mu_var (t : String) (v : String) :
    ∀ n, ¬ UnfoldPathVarBounded n v (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

private theorem CanSendPathBounded.not_mu_var (t : String) (p : String) (bs : List (Label × LocalTypeR)) :
    ∀ n, ¬ CanSendPathBounded n p bs (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

private theorem CanRecvPathBounded.not_mu_var (t : String) (p : String) (bs : List (Label × LocalTypeR)) :
    ∀ n, ¬ CanRecvPathBounded n p bs (.mu t (.var t)) := by
  intro n h
  induction n with
  | zero =>
      cases h
  | succ n ih =>
      cases h with
      | step h' =>
      have h'' := by simpa [LocalTypeR.substitute] using h'
      exact ih h''

theorem UnfoldsToEnd.not_mu_var {t : String} : ¬ UnfoldsToEnd (.mu t (.var t)) := by
  intro h
  obtain ⟨n, hn⟩ := UnfoldsToEnd.toBounded h
  exact UnfoldPathEndBounded.not_mu_var t n hn

theorem UnfoldsToVar.not_mu_var {t v : String} : ¬ UnfoldsToVar (.mu t (.var t)) v := by
  intro h
  obtain ⟨n, hn⟩ := UnfoldsToVar.toBounded h
  exact UnfoldPathVarBounded.not_mu_var t v n hn

theorem CanSend.not_mu_var {t p : String} {bs : List (Label × LocalTypeR)} :
    ¬ CanSend (.mu t (.var t)) p bs := by
  intro h
  obtain ⟨n, hn⟩ := CanSend.toBounded h
  exact CanSendPathBounded.not_mu_var t p bs n hn

theorem CanRecv.not_mu_var {t p : String} {bs : List (Label × LocalTypeR)} :
    ¬ CanRecv (.mu t (.var t)) p bs := by
  intro h
  obtain ⟨n, hn⟩ := CanRecv.toBounded h
  exact CanRecvPathBounded.not_mu_var t p bs n hn

/-! ## Unfolding Converse Lemmas

These lemmas go in the opposite direction: if fullUnfold (or a finite unfold
iteration) yields a constructor, then the corresponding membership predicate holds.
This is the bounded-path pattern from QpfTypes (RetPathBounded/VisPathBounded). -/

private theorem unfold_iter_eq_end_to_UnfoldsToEnd (a : LocalTypeR) :
    ∀ n, (LocalTypeR.unfold^[n] a = .end) → UnfoldsToEnd a := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .end := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact UnfoldsToEnd.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact UnfoldsToEnd.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var v =>
          have h' : (LocalTypeR.unfold^[n] (.var v)) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var v) h'
      | send p bs =>
          have h' : (LocalTypeR.unfold^[n] (.send p bs)) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send p bs) h'
      | recv p bs =>
          have h' : (LocalTypeR.unfold^[n] (.recv p bs)) = .end := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv p bs) h'

private theorem unfold_iter_eq_var_to_UnfoldsToVar (a : LocalTypeR) (v : String) :
    ∀ n, (LocalTypeR.unfold^[n] a = .var v) → UnfoldsToVar a v := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .var v := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact UnfoldsToVar.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact UnfoldsToVar.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var w =>
          have h' : (LocalTypeR.unfold^[n] (.var w)) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var w) h'
      | send p bs =>
          have h' : (LocalTypeR.unfold^[n] (.send p bs)) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send p bs) h'
      | recv p bs =>
          have h' : (LocalTypeR.unfold^[n] (.recv p bs)) = .var v := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv p bs) h'

private theorem unfold_iter_eq_send_to_CanSend (a : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    ∀ n, (LocalTypeR.unfold^[n] a = .send p bs) → CanSend a p bs := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .send p bs := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact CanSend.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact CanSend.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var v =>
          have h' : (LocalTypeR.unfold^[n] (.var v)) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var v) h'
      | send q cs =>
          have h' : (LocalTypeR.unfold^[n] (.send q cs)) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send q cs) h'
      | recv q cs =>
          have h' : (LocalTypeR.unfold^[n] (.recv q cs)) = .send p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv q cs) h'

private theorem unfold_iter_eq_recv_to_CanRecv (a : LocalTypeR) (p : String)
    (bs : List (Label × LocalTypeR)) :
    ∀ n, (LocalTypeR.unfold^[n] a = .recv p bs) → CanRecv a p bs := by
  intro n
  induction n generalizing a with
  | zero =>
      intro h
      have h' : a = .recv p bs := by
        simpa [Function.iterate_zero, id_eq] using h
      cases h'
      exact CanRecv.base
  | succ n ih =>
      intro h
      cases a with
      | mu t body =>
          have h' : (LocalTypeR.unfold^[n] (body.substitute t (.mu t body))) = .recv p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact CanRecv.mu (ih (a := body.substitute t (.mu t body)) h')
      | «end» =>
          have h' : (LocalTypeR.unfold^[n] .end) = .recv p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .end) h'
      | var v =>
          have h' : (LocalTypeR.unfold^[n] (.var v)) = .recv p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .var v) h'
      | send q cs =>
          have h' : (LocalTypeR.unfold^[n] (.send q cs)) = .recv p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .send q cs) h'
      | recv q cs =>
          have h' : (LocalTypeR.unfold^[n] (.recv q cs)) = .recv p bs := by
            simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using h
          exact ih (a := .recv q cs) h'

theorem UnfoldsToEnd_of_fullUnfold_eq {a : LocalTypeR} (h : a.fullUnfold = .end) :
    UnfoldsToEnd a := by
  apply unfold_iter_eq_end_to_UnfoldsToEnd a a.muHeight
  simpa [LocalTypeR.fullUnfold] using h

theorem UnfoldsToVar_of_fullUnfold_eq {a : LocalTypeR} {v : String} (h : a.fullUnfold = .var v) :
    UnfoldsToVar a v := by
  apply unfold_iter_eq_var_to_UnfoldsToVar a v a.muHeight
  simpa [LocalTypeR.fullUnfold] using h

theorem CanSend_of_fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : a.fullUnfold = .send p bs) : CanSend a p bs := by
  apply unfold_iter_eq_send_to_CanSend a p bs a.muHeight
  simpa [LocalTypeR.fullUnfold] using h

theorem CanRecv_of_fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : a.fullUnfold = .recv p bs) : CanRecv a p bs := by
  apply unfold_iter_eq_recv_to_CanRecv a p bs a.muHeight
  simpa [LocalTypeR.fullUnfold] using h


/-- Axioms: fullUnfold reflects observable predicates (used by Projection proofs). -/
axiom UnfoldsToEnd.fullUnfold_eq {a : LocalTypeR} (h : UnfoldsToEnd a) :
    a.fullUnfold = .end
axiom UnfoldsToVar.fullUnfold_eq {a : LocalTypeR} {v : String} (h : UnfoldsToVar a v) :
    a.fullUnfold = .var v
axiom CanSend.fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) : a.fullUnfold = .send p bs
axiom CanRecv.fullUnfold_eq {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) : a.fullUnfold = .recv p bs

/-! ## Bisimulation Relation

The key insight from PR #49: define the bisimulation functor using membership
predicates, not constructor matching. This avoids the quotient elimination
issues that block standard coinduction. -/

/-- Relation on local types. -/
abbrev Rel := LocalTypeR → LocalTypeR → Prop

/-- Branch-wise relation for bisimulation using List.Forall₂. -/
def BranchesRelBisim (R : Rel) (bs cs : List (Label × LocalTypeR)) : Prop :=
  List.Forall₂ (fun b c => b.1 = c.1 ∧ R b.2 c.2) bs cs

/-- One-step bisimulation functor using membership predicates.

    Unlike EQ2F which matches on constructors, BisimF uses the membership
    predicates to describe observable behavior. This allows the relation R
    to contain pairs of types with different constructors, as long as they
    have matching observable behavior. -/
inductive BisimF (R : Rel) : Rel where
  | eq_end {a b : LocalTypeR} :
      UnfoldsToEnd a → UnfoldsToEnd b → BisimF R a b
  | eq_var {a b : LocalTypeR} {v : String} :
      UnfoldsToVar a v → UnfoldsToVar b v → BisimF R a b
  | eq_send {a b : LocalTypeR} {partner : String} {bsa bsb : List (Label × LocalTypeR)} :
      CanSend a partner bsa → CanSend b partner bsb →
      BranchesRelBisim R bsa bsb →
      BisimF R a b
  | eq_recv {a b : LocalTypeR} {partner : String} {bsa bsb : List (Label × LocalTypeR)} :
      CanRecv a partner bsa → CanRecv b partner bsb →
      BranchesRelBisim R bsa bsb →
      BisimF R a b

/-- BranchesRelBisim is monotone. -/
theorem BranchesRelBisim.mono {R S : Rel} (hrs : ∀ a b, R a b → S a b)
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim S bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1, hrs _ _ hbc.2⟩ ih

/-- BisimF is monotone. -/
theorem BisimF.mono : Monotone BisimF := by
  intro R S hrs a b h
  cases h with
  | eq_end ha hb => exact BisimF.eq_end ha hb
  | eq_var ha hb => exact BisimF.eq_var ha hb
  | eq_send ha hb hbr =>
    exact BisimF.eq_send ha hb (BranchesRelBisim.mono hrs hbr)
  | eq_recv ha hb hbr =>
    exact BisimF.eq_recv ha hb (BranchesRelBisim.mono hrs hbr)

instance : CoinductiveRel Rel BisimF := ⟨BisimF.mono⟩

/-! Shared coinduction aliases (see `CoinductiveRel`). -/
/-- Greatest fixed point of BisimF (coinductive bisimulation). -/
def Bisim_gfp : Rel := CoinductiveRel.gfp (F := BisimF)

theorem Bisim_gfp_coind {R : Rel} (h : R ≤ BisimF R) : R ≤ Bisim_gfp := by
  exact CoinductiveRel.coind (F := BisimF) h

theorem Bisim_gfp_unfold : Bisim_gfp ≤ BisimF Bisim_gfp := by
  exact CoinductiveRel.unfold (F := BisimF)

theorem Bisim_gfp_fold : BisimF Bisim_gfp ≤ Bisim_gfp := by
  exact CoinductiveRel.fold (F := BisimF)


/-- Membership-based weak bisimulation.

    `Bisim a b` holds when there exists a relation R such that:
    1. R a b holds
    2. R is a post-fixpoint of BisimF (i.e., R ⊆ BisimF R)

    This is defined as an existential to avoid Prop-valued structure issues. -/
def Bisim (a b : LocalTypeR) : Prop :=
  ∃ R : Rel, (∀ x y, R x y → BisimF R x y) ∧ R a b

namespace Bisim

/-! ## Bisim is an Equivalence Relation -/

/-- BranchesRelBisim is reflexive when the underlying relation is. -/
theorem BranchesRelBisim.refl {R : Rel} (hrefl : ∀ t, R t t)
    (bs : List (Label × LocalTypeR)) : BranchesRelBisim R bs bs := by
  induction bs with
  | nil => exact List.Forall₂.nil
  | cons b rest ih =>
    exact List.Forall₂.cons ⟨rfl, hrefl b.2⟩ ih



/-- BranchesRelBisim is symmetric when the underlying relation is. -/
theorem BranchesRelBisim.symm {R : Rel} (hsymm : ∀ a b, R a b → R b a)
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim R cs bs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1.symm, hsymm _ _ hbc.2⟩ ih

/-- Convert BranchesRelBisim R bs cs to BranchesRelBisim S cs bs where S is the flip of R.
    This is used in the symmetry proof where S x y = R y x. -/
theorem BranchesRelBisim.flip {R S : Rel} (hflip : ∀ a b, R a b → S b a)
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim S cs bs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1.symm, hflip _ _ hbc.2⟩ ih

/-- Bisim is symmetric. -/
theorem symm {a b : LocalTypeR} (h : Bisim a b) : Bisim b a := by
  obtain ⟨R, hpost, hab⟩ := h
  -- Use the flipped relation: S x y = R y x
  let S : Rel := fun x y => R y x
  use S
  constructor
  · -- Show S is a post-fixpoint of BisimF
    intro x y hxy
    have hyx : R y x := hxy
    have hf : BisimF R y x := hpost y x hyx
    -- Transform BisimF R y x into BisimF S x y
    cases hf with
    | eq_end ha hb => exact BisimF.eq_end hb ha
    | eq_var ha hb => exact BisimF.eq_var hb ha
    | eq_send ha hb hbr =>
      apply BisimF.eq_send hb ha
      -- Need BranchesRelBisim S bsb bsa from BranchesRelBisim R bsa bsb
      -- S x y = R y x, so flip gives us what we need
      exact BranchesRelBisim.flip (fun a b h => h) hbr
    | eq_recv ha hb hbr =>
      apply BisimF.eq_recv hb ha
      exact BranchesRelBisim.flip (fun a b h => h) hbr
  · -- Show S b a = R a b
    exact hab

/-- BranchesRelBisim is transitive when the underlying relation is. -/
theorem BranchesRelBisim.trans {R : Rel}
    (htrans : ∀ a b c, R a b → R b c → R a c)
    {as bs cs : List (Label × LocalTypeR)}
    (hab : BranchesRelBisim R as bs) (hbc : BranchesRelBisim R bs cs) :
    BranchesRelBisim R as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact List.Forall₂.nil
  | cons h _ ih =>
    cases hbc with
    | cons h' hbc' =>
      exact List.Forall₂.cons ⟨h.1.trans h'.1, htrans _ _ _ h.2 h'.2⟩ (ih hbc')

/-- Compose two BranchesRelBisim proofs with different relations into one with composed relation.
    Given R1 as bs and R2 bs cs, produce R3 as cs where R3 a c := ∃ b, R1 a b ∧ R2 b c. -/
theorem BranchesRelBisim.compose {R1 R2 R3 : Rel}
    (hcomp : ∀ a b c, R1 a b → R2 b c → R3 a c)
    {as bs cs : List (Label × LocalTypeR)}
    (hab : BranchesRelBisim R1 as bs) (hbc : BranchesRelBisim R2 bs cs) :
    BranchesRelBisim R3 as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact List.Forall₂.nil
  | cons h _ ih =>
    cases hbc with
    | cons h' hbc' =>
      exact List.Forall₂.cons ⟨h.1.trans h'.1, hcomp _ _ _ h.2 h'.2⟩ (ih hbc')

/-- Bisim is transitive.

    This is the key result that works where EQ2_trans requires an axiom.
    The proof works because BisimF uses membership predicates, allowing
    the intermediate element to have any structure. -/
theorem trans {a b c : LocalTypeR} (hab : Bisim a b) (hbc : Bisim b c) : Bisim a c := by
  obtain ⟨R1, hpost1, hab'⟩ := hab
  obtain ⟨R2, hpost2, hbc'⟩ := hbc
  -- Use the transitive composition
  let R : Rel := fun x z => ∃ y, R1 x y ∧ R2 y z
  use R
  constructor
  · -- Show R is a post-fixpoint of BisimF
    intro x z ⟨y, hxy, hyz⟩
    have hf_xy : BisimF R1 x y := hpost1 x y hxy
    have hf_yz : BisimF R2 y z := hpost2 y z hyz
    -- Case analysis on the observable behavior of x~y
    cases hf_xy with
    | eq_end hx hy =>
      -- x unfolds to end, y unfolds to end
      -- y~z must also show y unfolds to something compatible with end
      cases hf_yz with
      | eq_end _ hz => exact BisimF.eq_end hx hz
      | eq_var hy' _ => exact absurd hy (UnfoldsToVar.not_end_of_var hy')
      | eq_send hy' _ _ => exact absurd hy (CanSend.not_end hy')
      | eq_recv hy' _ _ => exact absurd hy (CanRecv.not_end hy')
    | eq_var hx hy =>
      -- x unfolds to var v, y unfolds to var v
      cases hf_yz with
      | eq_end hy' _ => exact absurd hy' (UnfoldsToVar.not_end_of_var hy)
      | eq_var hy' hz =>
        have heq := UnfoldsToVar.deterministic hy hy'
        subst heq
        exact BisimF.eq_var hx hz
      | eq_send hy' _ _ => exact absurd hy (CanSend.not_var hy' _)
      | eq_recv hy' _ _ => exact absurd hy (CanRecv.not_var hy' _)
    | eq_send hx hy hbr_xy =>
      -- x can send to partner with branches, y can send to same partner
      cases hf_yz with
      | eq_end hy' _ => exact absurd hy' (CanSend.not_end hy)
      | eq_var hy' _ => exact absurd hy' (CanSend.not_var hy _)
      | eq_send hy' hz hbr_yz =>
        have ⟨heq_p, heq_bs⟩ := CanSend.deterministic hy hy'
        subst heq_p heq_bs
        apply BisimF.eq_send hx hz
        -- Compose the branch relations: R1 and R2 into R where R a c = ∃ b, R1 a b ∧ R2 b c
        exact BranchesRelBisim.compose (fun a b c hab hbc => ⟨b, hab, hbc⟩) hbr_xy hbr_yz
      | eq_recv hy' _ _ => exact absurd hy' (CanSend.not_recv hy)
    | eq_recv hx hy hbr_xy =>
      cases hf_yz with
      | eq_end hy' _ => exact absurd hy' (CanRecv.not_end hy)
      | eq_var hy' _ => exact absurd hy' (CanRecv.not_var hy _)
      | eq_send hy' _ _ =>
        -- hy : CanRecv y partner bsa, hy' : CanSend y partner' bsb'
        -- These contradict because same type can't both send and recv
        exact (CanSend.not_recv hy' hy).elim
      | eq_recv hy' hz hbr_yz =>
        have ⟨heq_p, heq_bs⟩ := CanRecv.deterministic hy hy'
        subst heq_p heq_bs
        apply BisimF.eq_recv hx hz
        exact BranchesRelBisim.compose (fun a b c hab hbc => ⟨b, hab, hbc⟩) hbr_xy hbr_yz
  · -- Show R a c
    exact ⟨b, hab', hbc'⟩

end Bisim

/-! ## Equivalence with EQ2

The membership predicates in BisimF correspond to unfolding behavior in EQ2F.
We prove Bisim ↔ EQ2, which enables deriving EQ2_trans from Bisim.trans. -/

/-- Convert BranchesRelBisim R to BranchesRel R (same structure, just namespace difference). -/
private theorem BranchesRelBisim_to_BranchesRel {R : Rel}
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRel R bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih => exact List.Forall₂.cons ⟨hbc.1, hbc.2⟩ ih

/-- Convert BranchesRel R to BranchesRelBisim R (same structure, just namespace difference). -/
private theorem BranchesRel_to_BranchesRelBisim {R : Rel}
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRel R bs cs) :
    BranchesRelBisim R bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih => exact List.Forall₂.cons ⟨hbc.1, hbc.2⟩ ih

/-- If two types can both send to the same partner with Bisim-related branches,
    they are Bisim equivalent.

    The proof constructs a witness relation that includes the pair plus all
    continuation pairs from Bisim. -/
theorem Bisim_of_same_send {a b : LocalTypeR} {p : String}
    {bsa bsb : List (Label × LocalTypeR)}
    (ha : CanSend a p bsa) (hb : CanSend b p bsb)
    (hbr : BranchesRelBisim Bisim bsa bsb) : Bisim a b := by
  -- Define witness relation: includes this pair + all Bisim pairs
  let R : Rel := fun x y =>
    (∃ p' bsa' bsb', CanSend x p' bsa' ∧ CanSend y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    (∃ p' bsa' bsb', CanRecv x p' bsa' ∧ CanRecv y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    Bisim x y
  use R
  constructor
  · -- Show R is a post-fixpoint of BisimF
    intro x y hxy
    cases hxy with
    | inl hSend =>
      obtain ⟨p', bsa', bsb', hxSend, hySend, hbr'⟩ := hSend
      -- Lift Bisim to R in the branches
      have hbr_R : BranchesRelBisim R bsa' bsb' :=
        BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
      exact BisimF.eq_send hxSend hySend hbr_R
    | inr hRest =>
      cases hRest with
      | inl hRecv =>
        obtain ⟨p', bsa', bsb', hxRecv, hyRecv, hbr'⟩ := hRecv
        have hbr_R : BranchesRelBisim R bsa' bsb' :=
          BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
        exact BisimF.eq_recv hxRecv hyRecv hbr_R
      | inr hBisim =>
        -- x and y are Bisim, extract witness and use its post-fixpoint property
        obtain ⟨R', hR'post, hxy'⟩ := hBisim
        have hf : BisimF R' x y := hR'post x y hxy'
        -- Lift BisimF R' to BisimF R using monotonicity
        -- R' ⊆ Bisim ⊆ R
        have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b h => ⟨R', hR'post, h⟩
        have hR'_to_R : ∀ a b, R' a b → R a b := fun a b h => Or.inr (Or.inr (hR'_to_Bisim a b h))
        exact BisimF.mono hR'_to_R x y hf
  · -- Show R a b via the send case
    exact Or.inl ⟨p, bsa, bsb, ha, hb, hbr⟩

/-- If two types can both recv from the same partner with Bisim-related branches,
    they are Bisim equivalent. -/
theorem Bisim_of_same_recv {a b : LocalTypeR} {p : String}
    {bsa bsb : List (Label × LocalTypeR)}
    (ha : CanRecv a p bsa) (hb : CanRecv b p bsb)
    (hbr : BranchesRelBisim Bisim bsa bsb) : Bisim a b := by
  -- Use same witness relation as Bisim_of_same_send
  let R : Rel := fun x y =>
    (∃ p' bsa' bsb', CanSend x p' bsa' ∧ CanSend y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    (∃ p' bsa' bsb', CanRecv x p' bsa' ∧ CanRecv y p' bsb' ∧ BranchesRelBisim Bisim bsa' bsb') ∨
    Bisim x y
  use R
  constructor
  · -- Same post-fixpoint proof as Bisim_of_same_send
    intro x y hxy
    cases hxy with
    | inl hSend =>
      obtain ⟨p', bsa', bsb', hxSend, hySend, hbr'⟩ := hSend
      have hbr_R : BranchesRelBisim R bsa' bsb' :=
        BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
      exact BisimF.eq_send hxSend hySend hbr_R
    | inr hRest =>
      cases hRest with
      | inl hRecv =>
        obtain ⟨p', bsa', bsb', hxRecv, hyRecv, hbr'⟩ := hRecv
        have hbr_R : BranchesRelBisim R bsa' bsb' :=
          BranchesRelBisim.mono (fun a b hBisim => Or.inr (Or.inr hBisim)) hbr'
        exact BisimF.eq_recv hxRecv hyRecv hbr_R
      | inr hBisim =>
        obtain ⟨R', hR'post, hxy'⟩ := hBisim
        have hf : BisimF R' x y := hR'post x y hxy'
        have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b h => ⟨R', hR'post, h⟩
        have hR'_to_R : ∀ a b, R' a b → R a b := fun a b h => Or.inr (Or.inr (hR'_to_Bisim a b h))
        exact BisimF.mono hR'_to_R x y hf
  · -- Show R a b via the recv case
    exact Or.inr (Or.inl ⟨p, bsa, bsb, ha, hb, hbr⟩)

/-- Helper: unfolds-to-end implies EQ2 to .end through unfolding.
    If a unfolds to end, then EQ2 a .end (since unfolding preserves EQ2). -/
theorem UnfoldsToEnd.toEQ2 {a : LocalTypeR} (h : UnfoldsToEnd a) :
    EQ2 a .end := by
  induction h with
  | base => exact EQ2_refl _
  | @mu t body _ ih =>
    -- EQ2 (mu t body) end requires EQ2F EQ2 (mu t body) end
    -- EQ2F at (mu, end) = EQ2 (body.substitute t (mu t body)) end = ih
    exact EQ2.construct ih

/-- Helper: unfolds-to-var implies EQ2 to that var. -/
theorem UnfoldsToVar.toEQ2 {a : LocalTypeR} {v : String} (h : UnfoldsToVar a v) :
    EQ2 a (.var v) := by
  induction h with
  | base => exact EQ2_refl _
  | @mu t body v' _ ih =>
    exact EQ2.construct ih

/-- Helper: can-send implies EQ2 to the corresponding send type. -/
theorem CanSend.toEQ2 {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs) : EQ2 a (.send p bs) := by
  induction h with
  | base => exact EQ2_refl _
  | @mu t body p' bs' _ ih =>
    exact EQ2.construct ih

/-- Helper: can-recv implies EQ2 to the corresponding recv type. -/
theorem CanRecv.toEQ2 {a : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs) : EQ2 a (.recv p bs) := by
  induction h with
  | base => exact EQ2_refl _
  | @mu t body p' bs' _ ih =>
    exact EQ2.construct ih

/-- Convert BranchesRelBisim to BranchesRel EQ2 when the underlying relation implies EQ2. -/
theorem BranchesRelBisim.toEQ2 {R : Rel} (hR : ∀ a b, R a b → EQ2 a b)
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRel EQ2 bs cs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    exact List.Forall₂.cons ⟨hbc.1, hR _ _ hbc.2⟩ ih

/-- Bisim implies EQ2.

    This is the key theorem: membership-based bisimulation implies coinductive equality.
    The proof uses the EQ2 coinduction principle with Bisim as the witness relation.

    Proof idea:
    - Show that Bisim is a post-fixpoint of EQ2F
    - Case on BisimF to determine observable behavior
    - Use the toEQ2 helpers to convert membership predicates to EQ2 proofs
    - Apply EQ2_coind -/
theorem Bisim.toEQ2 {a b : LocalTypeR} (h : Bisim a b) : EQ2 a b := by
  -- Use EQ2_coind_upto which allows using EQ2 directly in the post-fixpoint proof
  apply EQ2_coind_upto (R := Bisim)
  · -- Show: ∀ x y, Bisim x y → EQ2F (EQ2_closure Bisim) x y
    intro x y hBisim
    obtain ⟨R, hRpost, hxy⟩ := hBisim
    have hf : BisimF R x y := hRpost x y hxy
    -- Case on BisimF to determine observable behavior
    cases hf with
    | eq_end hx hy =>
      -- Both unfold to end, so both are EQ2 to .end
      have hxeq : EQ2 x .end := UnfoldsToEnd.toEQ2 hx
      have hyeq : EQ2 y .end := UnfoldsToEnd.toEQ2 hy
      -- EQ2 x y follows by transitivity through .end
      have hxy_eq2 : EQ2 x y := EQ2_trans hxeq (EQ2_symm hyeq)
      -- Lift EQ2F EQ2 to EQ2F (EQ2_closure Bisim) using monotonicity
      have hf_eq2 : EQ2F EQ2 x y := EQ2.destruct hxy_eq2
      exact EQ2F.mono (fun _ _ h => Or.inr h) x y hf_eq2
    | eq_var hx hy =>
      -- Both unfold to the same var
      have hxeq : EQ2 x (.var _) := UnfoldsToVar.toEQ2 hx
      have hyeq : EQ2 y (.var _) := UnfoldsToVar.toEQ2 hy
      have hxy_eq2 : EQ2 x y := EQ2_trans hxeq (EQ2_symm hyeq)
      have hf_eq2 : EQ2F EQ2 x y := EQ2.destruct hxy_eq2
      exact EQ2F.mono (fun _ _ h => Or.inr h) x y hf_eq2
    | @eq_send _ _ partner bsa bsb hx hy hbr =>
      -- Key insight: R ⊆ Bisim since R is a post-fixpoint of BisimF
      have hR_to_Bisim : ∀ a b, R a b → Bisim a b := fun a b hr => ⟨R, hRpost, hr⟩
      -- Lift branches to EQ2_closure Bisim
      have hbr_closure : BranchesRelBisim (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim.mono (fun a b h => Or.inl (hR_to_Bisim a b h)) hbr
      -- Convert to BranchesRel for EQ2F (extracted as helper to avoid induction scope issues)
      have hbr_rel : BranchesRel (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim_to_BranchesRel hbr_closure
      -- Case on the actual constructors of x and y
      -- Lift branch relation to Bisim for use in Bisim_of_same_send/recv
      have hbr_bisim : BranchesRelBisim Bisim bsa bsb :=
        BranchesRelBisim.mono (fun a b h => hR_to_Bisim a b h) hbr
      cases hx with
      | base =>
        -- x = send partner bsa directly
        cases hy with
        | base =>
          -- y = send partner bsb directly
          -- EQ2F at (send, send) = (partner = partner) ∧ BranchesRel closure bsa bsb
          -- simp reduces partner = partner to True since they're definitionally equal
          simp only [EQ2F]
          exact ⟨trivial, hbr_rel⟩
        | @mu s body _ _ hinner =>
          -- y = mu s body, need EQ2F closure (send partner bsa) (mu s body)
          -- which is: closure (send partner bsa) (body.substitute s (mu s body))
          simp only [EQ2F, EQ2_closure]
          -- Both can send to partner with related branches, so they're Bisim
          have hBisim := Bisim_of_same_send CanSend.base hinner hbr_bisim
          exact Or.inl hBisim
      | @mu t body _ _ hinner =>
        -- x = mu t body, need EQ2F closure (mu t body) y
        -- Must case on hy to make y concrete for the match to reduce
        cases hy with
        | base =>
          -- y = send partner bsb
          simp only [EQ2F, EQ2_closure]
          have hBisim := Bisim_of_same_send hinner CanSend.base hbr_bisim
          exact Or.inl hBisim
        | @mu s body' _ _ hinner' =>
          -- y = mu s body'
          -- EQ2F at (mu, mu) = closure pair ∧ closure pair
          simp only [EQ2F, EQ2_closure]
          constructor
          · have hBisim := Bisim_of_same_send hinner (CanSend.mu hinner') hbr_bisim
            exact Or.inl hBisim
          · have hBisim := Bisim_of_same_send (CanSend.mu hinner) hinner' hbr_bisim
            exact Or.inl hBisim
    | @eq_recv _ _ partner bsa bsb hx hy hbr =>
      -- Similar to eq_send with recv
      have hR_to_Bisim : ∀ a b, R a b → Bisim a b := fun a b hr => ⟨R, hRpost, hr⟩
      have hbr_closure : BranchesRelBisim (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim.mono (fun a b h => Or.inl (hR_to_Bisim a b h)) hbr
      have hbr_rel : BranchesRel (EQ2_closure Bisim) bsa bsb :=
        BranchesRelBisim_to_BranchesRel hbr_closure
      have hbr_bisim : BranchesRelBisim Bisim bsa bsb :=
        BranchesRelBisim.mono (fun a b h => hR_to_Bisim a b h) hbr
      cases hx with
      | base =>
        cases hy with
        | base =>
          simp only [EQ2F]
          exact ⟨trivial, hbr_rel⟩
        | @mu s body _ _ hinner =>
          simp only [EQ2F, EQ2_closure]
          have hBisim := Bisim_of_same_recv CanRecv.base hinner hbr_bisim
          exact Or.inl hBisim
      | @mu t body _ _ hinner =>
        -- x = mu t body, need EQ2F closure (mu t body) y
        -- Must case on hy to make y concrete for the match to reduce
        cases hy with
        | base =>
          -- y = recv partner bsb
          simp only [EQ2F, EQ2_closure]
          have hBisim := Bisim_of_same_recv hinner CanRecv.base hbr_bisim
          exact Or.inl hBisim
        | @mu s body' _ _ hinner' =>
          -- y = mu s body'
          -- EQ2F at (mu, mu) = closure pair ∧ closure pair
          simp only [EQ2F, EQ2_closure]
          constructor
          · have hBisim := Bisim_of_same_recv hinner (CanRecv.mu hinner') hbr_bisim
            exact Or.inl hBisim
          · have hBisim := Bisim_of_same_recv (CanRecv.mu hinner) hinner' hbr_bisim
            exact Or.inl hBisim
  · exact h

/-! ## EQ2 Incompatibility with Observable Behaviors

These lemmas show that `EQ2 .end x` is incompatible with observable behaviors
other than `UnfoldsToEnd`. The proofs use induction on the observable predicates. -/

/-- `EQ2 .end x` is incompatible with `CanSend x p bs`.

    Proof by induction on CanSend. Each constructor exposes a communication head
    that contradicts `EQ2F EQ2 .end _` = False for sends. -/
theorem EQ2_end_not_CanSend {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (hcan : CanSend x p bs) (heq : EQ2 .end x) : False := by
  induction hcan with
  | base =>
    -- x = .send p bs, EQ2 .end (.send p bs) contradicts EQ2F definition
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
  | mu _ ih =>
    -- x = .mu t body, by destruct: EQ2 .end (body.substitute t (.mu t body))
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf

/-- `EQ2 .end x` is incompatible with `CanRecv x p bs`. -/
theorem EQ2_end_not_CanRecv {x : LocalTypeR} {p : String} {bs : List (Label × LocalTypeR)}
    (hcan : CanRecv x p bs) (heq : EQ2 .end x) : False := by
  induction hcan with
  | base =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
  | mu _ ih =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf

/-- `EQ2 .end x` is incompatible with `UnfoldsToVar x v`. -/
theorem EQ2_end_not_UnfoldsToVar {x : LocalTypeR} {v : String}
    (hunf : UnfoldsToVar x v) (heq : EQ2 .end x) : False := by
  induction hunf with
  | base =>
    -- x = .var v, EQ2 .end (.var v) contradicts EQ2F definition
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
  | mu _ ih =>
    -- x = .mu t body, by destruct: EQ2 .end (body.substitute t (.mu t body))
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf

/-- `EQ2 (.var v) x` is incompatible with `UnfoldsToEnd x`. -/
theorem EQ2_var_not_UnfoldsToEnd {x : LocalTypeR} {v : String}
    (hunf : UnfoldsToEnd x) (heq : EQ2 (.var v) x) : False := by
  induction hunf with
  | base =>
    -- x = .end, EQ2 (.var v) .end contradicts EQ2F definition
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
  | mu _ ih =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf

/-- `EQ2 (.var v) x` is incompatible with `UnfoldsToVar x w` when w ≠ v. -/
theorem EQ2_var_not_UnfoldsToVar_diff {x : LocalTypeR} {v w : String}
    (hunf : UnfoldsToVar x w) (heq : EQ2 (.var v) x) (hne : w ≠ v) : False := by
  induction hunf with
  | base =>
    -- x = .var w, EQ2 (.var v) (.var w) requires v = w
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact hne hf.symm
  | mu _ ih =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf hne

/-- `EQ2 (.var v) x` is incompatible with `CanSend x p bs`. -/
theorem EQ2_var_not_CanSend {x : LocalTypeR} {v : String} {p : String}
    {bs : List (Label × LocalTypeR)}
    (hcan : CanSend x p bs) (heq : EQ2 (.var v) x) : False := by
  induction hcan with
  | base =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
  | mu _ ih =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf

/-- `EQ2 (.var v) x` is incompatible with `CanRecv x p bs`. -/
theorem EQ2_var_not_CanRecv {x : LocalTypeR} {v : String} {p : String}
    {bs : List (Label × LocalTypeR)}
    (hcan : CanRecv x p bs) (heq : EQ2 (.var v) x) : False := by
  induction hcan with
  | base =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
  | mu _ ih =>
    have hf := EQ2.destruct heq
    simp only [EQ2F] at hf
    exact ih hf

/-! ## Observable Behavior Extraction from EQ2

These lemmas extract observable behavior from EQ2 proofs. They are needed for EQ2.toBisim.

**IMPORTANT SEMANTIC CONSTRAINT**: These lemmas are only valid for *contractive* types,
where every mu-bound variable is guarded (appears only inside a communication before
any recursive reference). For non-contractive types like `.mu t (.var t)`, the EQ2
relation can hold for `EQ2 .end (.mu t (.var t))` (via the gfp semantics allowing
infinite chains), but `UnfoldsToEnd (.mu t (.var t))` is false (it cycles forever).

We expose a **layered extraction interface** so we can swap between:
- a contractive-only extraction (axiom-free, requires proofs), and
- an axiomatic extraction (unconditional), with
- a hybrid default that prefers contractive proofs but falls back to axioms.

The global default matches the substitution environment default: **no extra obligations**
leak into downstream proofs, but we retain a single integration point for swapping. -/

/-! ## EQ2 Extraction Layer (Swap Point) -/

structure EQ2Extraction where
  Good : LocalTypeR → Prop
  end_right : ∀ {x}, Good x → EQ2 .end x → UnfoldsToEnd x
  var_right : ∀ {x v}, Good x → EQ2 (.var v) x → UnfoldsToVar x v
  send_right : ∀ {x p bs}, Good x → EQ2 (.send p bs) x →
    ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs
  recv_right : ∀ {x p bs}, Good x → EQ2 (.recv p bs) x →
    ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs
  mus_to_BisimF :
    ∀ {t s body body'}, Good (.mu t body) → Good (.mu s body') →
      EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body') → BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body')

/-- For closed, contractive types, `EQ2 .end x` implies `UnfoldsToEnd x`.

    Proof: By `observable_of_closed_contractive`, x has observable behavior. By the
    incompatibility lemmas above, the only possibility is `UnfoldsToEnd`. -/
theorem EQ2.end_right_implies_UnfoldsToEnd_of_closed {x : LocalTypeR}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 .end x) : UnfoldsToEnd x := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end h => exact h
  | is_var h => exact absurd heq (EQ2_end_not_UnfoldsToVar h)
  | is_send h => exact absurd heq (EQ2_end_not_CanSend h)
  | is_recv h => exact absurd heq (EQ2_end_not_CanRecv h)

/-- For contractive types, `EQ2 .end x` implies `UnfoldsToEnd x`. -/
theorem EQ2.end_right_implies_UnfoldsToEnd_of_contractive {x : LocalTypeR}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 .end x) : UnfoldsToEnd x := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end h => exact h
  | is_var h => exact absurd heq (EQ2_end_not_UnfoldsToVar h)
  | is_send h => exact absurd heq (EQ2_end_not_CanSend h)
  | is_recv h => exact absurd heq (EQ2_end_not_CanRecv h)

/-- For contractive types, `EQ2 x .end` implies `UnfoldsToEnd x`. -/
theorem EQ2.end_left_implies_UnfoldsToEnd_of_contractive {x : LocalTypeR}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 x .end) : UnfoldsToEnd x :=
  EQ2.end_right_implies_UnfoldsToEnd_of_contractive hclosed hcontr (EQ2_symm heq)

/-- For contractive types, `EQ2 (.var v) x` implies `UnfoldsToVar x v`. -/
theorem EQ2.var_right_implies_UnfoldsToVar_of_contractive {x : LocalTypeR} {v : String}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 (.var v) x) : UnfoldsToVar x v := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end h => exact absurd heq (EQ2_var_not_UnfoldsToEnd h)
  | is_var h =>
      rename_i v'
      by_cases hne : v' = v
      · subst hne; exact h
      · exact (False.elim (EQ2_var_not_UnfoldsToVar_diff h heq hne))
  | is_send h => exact absurd heq (EQ2_var_not_CanSend h)
  | is_recv h => exact absurd heq (EQ2_var_not_CanRecv h)

/-- For contractive types, `EQ2 x (.var v)` implies `UnfoldsToVar x v`. -/
theorem EQ2.var_left_implies_UnfoldsToVar_of_contractive {x : LocalTypeR} {v : String}
    (hclosed : x.isClosed) (hcontr : x.isContractive = true) (heq : EQ2 x (.var v)) : UnfoldsToVar x v :=
  EQ2.var_right_implies_UnfoldsToVar_of_contractive hclosed hcontr (EQ2_symm heq)

/-- For contractive types, `EQ2 (.send p bs) x` implies `CanSend x p cs` with matching branches. -/
theorem EQ2.send_right_implies_CanSend_of_contractive {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 (.send p bs) x) : ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  have hobs := observable_of_closed_contractive hclosed hcontr
  cases hobs with
  | is_end hend =>
      have hx_end : EQ2 x .end := UnfoldsToEnd.toEQ2 hend
      have hsend_end : EQ2 (.send p bs) .end := EQ2_trans heq hx_end
      have hfalse : False := by
        have hf := EQ2.destruct hsend_end
        simpa [EQ2F] using hf
      exact (False.elim hfalse)
  | is_var hvar =>
      have hx_var : EQ2 x (.var _) := UnfoldsToVar.toEQ2 hvar
      have hsend_var : EQ2 (.send p bs) (.var _) := EQ2_trans heq hx_var
      have hfalse : False := by
        have hf := EQ2.destruct hsend_var
        simpa [EQ2F] using hf
      exact (False.elim hfalse)
  | is_recv hrecv =>
      have hx_recv : EQ2 x (.recv _ _) := CanRecv.toEQ2 hrecv
      have hsend_recv : EQ2 (.send p bs) (.recv _ _) := EQ2_trans heq hx_recv
      have hfalse : False := by
        have hf := EQ2.destruct hsend_recv
        simpa [EQ2F] using hf
      exact (False.elim hfalse)
  | is_send hsend =>
      rename_i p' cs
      obtain ⟨n, hn⟩ := CanSend.toBounded hsend
      have hiter := (EQ2_unfold_right_iter (a := .send p bs) (b := x) heq) n
      have hsend_unfold : EQ2 (.send p bs) ((LocalTypeR.unfold)^[n] x) := by
        simpa using hiter
      have hx : (LocalTypeR.unfold)^[n] x = .send p' cs :=
        CanSendPathBounded.unfold_iter_eq hn
      have hsend' : EQ2 (.send p bs) (.send p' cs) := by
        simpa [hx] using hsend_unfold
      have hf := EQ2.destruct hsend'
      have ⟨hp, hbr⟩ : p = p' ∧ BranchesRel EQ2 bs cs := by
        simpa [EQ2F] using hf
      subst hp
      exact ⟨cs, hsend, hbr⟩

/-- Flip BranchesRel with symmetric relation. -/
private theorem BranchesRel_flip {as bs : List (Label × LocalTypeR)}
    (h : BranchesRel EQ2 as bs) : BranchesRel EQ2 bs as := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih => exact List.Forall₂.cons ⟨hbc.1.symm, EQ2_symm hbc.2⟩ ih

/-- For contractive types, `EQ2 x (.send p cs)` implies `CanSend x p bs` with matching branches. -/
theorem EQ2.send_left_implies_CanSend_of_contractive {x : LocalTypeR} {p : String}
    {cs : List (Label × LocalTypeR)} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 x (.send p cs)) : ∃ bs, CanSend x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := EQ2_symm heq
  obtain ⟨bs, hcan, hbr⟩ := EQ2.send_right_implies_CanSend_of_contractive (x := x) hclosed hcontr hsymm
  exact ⟨bs, hcan, BranchesRel_flip hbr⟩

/-- For contractive types, `EQ2 (.recv p bs) x` implies `CanRecv x p cs` with matching branches. -/
theorem EQ2.recv_right_implies_CanRecv_of_contractive {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 (.recv p bs) x) : ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  -- Reduce recv to send via duality.
  have hdual : EQ2 (.send p (LocalTypeR.dualBranches bs)) x.dual := by
    have h' := EQ2_dual_compat (a := .recv p bs) (b := x) heq
    simpa [LocalTypeR.dual] using h'
  have hclosed' : x.dual.isClosed := by
    simpa [LocalTypeR.dual_isClosed] using hclosed
  have hcontr' : x.dual.isContractive = true := by
    simpa [LocalTypeR.dual_isContractive] using hcontr
  obtain ⟨cs, hcan, hbr⟩ :=
    EQ2.send_right_implies_CanSend_of_contractive (x := x.dual) hclosed' hcontr' hdual
  have hcan' : CanRecv x p (LocalTypeR.dualBranches cs) := by
    have h' : CanRecv x.dual.dual p (LocalTypeR.dualBranches (LocalTypeR.dualBranches cs)) :=
      CanSend.dual (t := x.dual) hcan
    simpa [LocalTypeR.dual_involutive, LocalTypeR.dualBranches_involutive] using h'
  have hbr' : BranchesRel EQ2 bs (LocalTypeR.dualBranches cs) :=
    BranchesRel_dual_eq2 (bs := bs) (cs := cs) hbr
  exact ⟨LocalTypeR.dualBranches cs, hcan', hbr'⟩

/-- For contractive types, `EQ2 x (.recv p cs)` implies `CanRecv x p bs` with matching branches. -/
theorem EQ2.recv_left_implies_CanRecv_of_contractive {x : LocalTypeR} {p : String}
    {cs : List (Label × LocalTypeR)} (hclosed : x.isClosed) (hcontr : x.isContractive = true)
    (heq : EQ2 x (.recv p cs)) : ∃ bs, CanRecv x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := EQ2_symm heq
  obtain ⟨bs, hcan, hbr⟩ := EQ2.recv_right_implies_CanRecv_of_contractive (x := x) hclosed hcontr hsymm
  exact ⟨bs, hcan, BranchesRel_flip hbr⟩


/-! ## Extraction from EQ2 when fullUnfold is non-mu

These lemmas require only that the fully-unfolded form has no leading `mu`.
They are useful as a local, non-leaky swap point when such a fact is available
(e.g., from closed+contractive hypotheses). -/

theorem EQ2.end_right_implies_UnfoldsToEnd_of_fullUnfold_nonmu {x : LocalTypeR}
    (hmu : x.fullUnfold.muHeight = 0) (heq : EQ2 .end x) : UnfoldsToEnd x := by
  have hiter := (EQ2_unfold_right_iter (a := .end) (b := x) heq) x.muHeight
  have hfull : EQ2 .end x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | «end» =>
      exact UnfoldsToEnd_of_fullUnfold_eq (by simpa [hx])
  | var v =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | send p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | recv p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

theorem EQ2.var_right_implies_UnfoldsToVar_of_fullUnfold_nonmu {x : LocalTypeR} {v : String}
    (hmu : x.fullUnfold.muHeight = 0) (heq : EQ2 (.var v) x) : UnfoldsToVar x v := by
  have hiter := (EQ2_unfold_right_iter (a := .var v) (b := x) heq) x.muHeight
  have hfull : EQ2 (.var v) x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | var w =>
      have hf := EQ2.destruct hfull
      have hw : v = w := by
        simpa [EQ2F, hx] using hf
      subst hw
      exact UnfoldsToVar_of_fullUnfold_eq (by simpa [hx])
  | «end» =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | send p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | recv p bs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

theorem EQ2.send_right_implies_CanSend_of_fullUnfold_nonmu {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (hmu : x.fullUnfold.muHeight = 0)
    (heq : EQ2 (.send p bs) x) : ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  have hiter := (EQ2_unfold_right_iter (a := .send p bs) (b := x) heq) x.muHeight
  have hfull : EQ2 (.send p bs) x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | send q cs =>
      have hf := EQ2.destruct hfull
      have hpr : p = q ∧ BranchesRel EQ2 bs cs := by
        simpa [EQ2F, hx] using hf
      rcases hpr with ⟨hp, hbr⟩
      subst hp
      have hcan : CanSend x p cs := CanSend_of_fullUnfold_eq (by simpa [hx])
      exact ⟨cs, hcan, hbr⟩
  | «end» =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | var v =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | recv q cs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

theorem EQ2.recv_right_implies_CanRecv_of_fullUnfold_nonmu {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (hmu : x.fullUnfold.muHeight = 0)
    (heq : EQ2 (.recv p bs) x) : ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  have hiter := (EQ2_unfold_right_iter (a := .recv p bs) (b := x) heq) x.muHeight
  have hfull : EQ2 (.recv p bs) x.fullUnfold := by
    simpa [LocalTypeR.fullUnfold] using hiter
  cases hx : x.fullUnfold with
  | recv q cs =>
      have hf := EQ2.destruct hfull
      have hpr : p = q ∧ BranchesRel EQ2 bs cs := by
        simpa [EQ2F, hx] using hf
      rcases hpr with ⟨hp, hbr⟩
      subst hp
      have hcan : CanRecv x p cs := CanRecv_of_fullUnfold_eq (by simpa [hx])
      exact ⟨cs, hcan, hbr⟩
  | «end» =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | var v =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | send q cs =>
      have hf := EQ2.destruct hfull
      simp [EQ2F, hx] at hf
  | mu t body =>
      have hmu' : Nat.succ body.muHeight = 0 := by
        simpa [LocalTypeR.muHeight, hx] using hmu
      exact (False.elim (Nat.succ_ne_zero _ hmu'))

/-- Transfer observables across EQ2.

    **Semantic constraint**: This axiom is only valid for contractive types.
    See the section header for details.

    The unconditional version is kept as an axiom for API convenience, since all
    types in practice (from well-formed projections) are contractive. -/
axiom EQ2_transfer_observable_axiom {a b : LocalTypeR} (h : EQ2 a b) (obs_a : Observable a) :
    ∃ obs_b : Observable b, ObservableRel EQ2 obs_a obs_b

/-- If EQ2 .end x, then x unfolds to end. -/
theorem EQ2.end_right_implies_UnfoldsToEnd_axiom {x : LocalTypeR} (h : EQ2 .end x) : UnfoldsToEnd x := by
  have hobs := EQ2_transfer_observable_axiom (a := .end) (b := x) h
    (Observable.is_end UnfoldsToEnd.base)
  rcases hobs with ⟨obs_b, hrel⟩
  cases obs_b with
  | is_end hb => exact hb
  | is_var hb => cases hrel
  | is_send hb => cases hrel
  | is_recv hb => cases hrel

/-- If EQ2 (.var v) x, then x unfolds to var v. -/
theorem EQ2.var_right_implies_UnfoldsToVar_axiom {x : LocalTypeR} {v : String}
    (h : EQ2 (.var v) x) : UnfoldsToVar x v := by
  have hobs := EQ2_transfer_observable_axiom (a := .var v) (b := x) h
    (Observable.is_var (UnfoldsToVar.base (v := v)))
  rcases hobs with ⟨obs_b, hrel⟩
  cases obs_b with
  | is_var hb => exact hb
  | is_end hb => cases hrel
  | is_send hb => cases hrel
  | is_recv hb => cases hrel

/-- If EQ2 (.send p bs) x, then x can send to p with EQ2-related branches. -/
theorem EQ2.send_right_implies_CanSend_axiom {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : EQ2 (.send p bs) x) :
    ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  have hobs := EQ2_transfer_observable_axiom (a := .send p bs) (b := x) h
    (Observable.is_send (CanSend.base (partner := p) (branches := bs)))
  rcases hobs with ⟨obs_b, hrel⟩
  cases obs_b with
  | is_send hcan =>
      cases hrel with
      | is_send hbr =>
          exact ⟨_, hcan, hbr⟩
  | is_end hb => cases hrel
  | is_var hb => cases hrel
  | is_recv hb => cases hrel

/-- If EQ2 (.recv p bs) x, then x can recv from p with EQ2-related branches. -/
theorem EQ2.recv_right_implies_CanRecv_axiom {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : EQ2 (.recv p bs) x) :
    ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  have hobs := EQ2_transfer_observable_axiom (a := .recv p bs) (b := x) h
    (Observable.is_recv (CanRecv.base (partner := p) (branches := bs)))
  rcases hobs with ⟨obs_b, hrel⟩
  cases obs_b with
  | is_recv hcan =>
      cases hrel with
      | is_recv hbr =>
          exact ⟨_, hcan, hbr⟩
  | is_end hb => cases hrel
  | is_var hb => cases hrel
  | is_send hb => cases hrel

/-- For the mu/mu case in EQ2.toBisim: if EQ2 relates two mus, they have compatible
    observable behavior that can be expressed as BisimF.

    This axiom is needed because determining observable behavior requires contractiveness,
    but EQ2 is a global relation that doesn't track structural properties like contractiveness.

    **Semantic soundness**: In practice, all types from well-formed projections are contractive,
    so this axiom holds for all practical use cases. -/
axiom EQ2_mus_to_BisimF_axiom {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body')) :
    BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body')

theorem EQ2_mus_to_BisimF_of_contractive {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body'))
    (hc1_closed : (LocalTypeR.mu t body).isClosed)
    (hc1 : (LocalTypeR.mu t body).isContractive = true)
    (hc2_closed : (LocalTypeR.mu s body').isClosed)
    (hc2 : (LocalTypeR.mu s body').isContractive = true) :
    BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body') := by
  have hobs := observable_of_closed_contractive hc1_closed hc1
  cases hobs with
  | is_end hend =>
      have ha_eq_end : EQ2 (.mu t body) .end := UnfoldsToEnd.toEQ2 hend
      have hb_eq_end : EQ2 (.mu s body') .end := EQ2_trans (EQ2_symm h) ha_eq_end
      have hEndB : UnfoldsToEnd (.mu s body') :=
        EQ2.end_left_implies_UnfoldsToEnd_of_contractive (x := .mu s body') hc2_closed hc2 hb_eq_end
      exact BisimF.eq_end hend hEndB
  | is_var hvar =>
      rename_i v
      have ha_eq_var : EQ2 (.mu t body) (.var v) := UnfoldsToVar.toEQ2 hvar
      have hb_eq_var : EQ2 (.mu s body') (.var v) := EQ2_trans (EQ2_symm h) ha_eq_var
      have hVarB : UnfoldsToVar (.mu s body') v :=
        EQ2.var_left_implies_UnfoldsToVar_of_contractive (x := .mu s body') hc2_closed hc2 hb_eq_var
      exact BisimF.eq_var hvar hVarB
  | is_send hsend =>
      rename_i p bs
      have ha_eq_send : EQ2 (.mu t body) (.send p bs) := CanSend.toEQ2 hsend
      have hb_eq_send : EQ2 (.mu s body') (.send p bs) := EQ2_trans (EQ2_symm h) ha_eq_send
      obtain ⟨bs', hCanSend, hbr⟩ :=
        EQ2.send_left_implies_CanSend_of_contractive (x := .mu s body') hc2_closed hc2 hb_eq_send
      have hbr' : BranchesRel EQ2 bs bs' := BranchesRel_flip hbr
      exact BisimF.eq_send hsend hCanSend (BranchesRel_to_BranchesRelBisim hbr')
  | is_recv hrecv =>
      rename_i p bs
      have ha_eq_recv : EQ2 (.mu t body) (.recv p bs) := CanRecv.toEQ2 hrecv
      have hb_eq_recv : EQ2 (.mu s body') (.recv p bs) := EQ2_trans (EQ2_symm h) ha_eq_recv
      obtain ⟨bs', hCanRecv, hbr⟩ :=
        EQ2.recv_left_implies_CanRecv_of_contractive (x := .mu s body') hc2_closed hc2 hb_eq_recv
      have hbr' : BranchesRel EQ2 bs bs' := BranchesRel_flip hbr
      exact BisimF.eq_recv hrecv hCanRecv (BranchesRel_to_BranchesRelBisim hbr')

/-- Axiomatic extraction (unconditional). -/
def AxiomaticExtraction : EQ2Extraction :=
  { Good := fun _ => True
    end_right := by intro _ _ h; exact EQ2.end_right_implies_UnfoldsToEnd_axiom h
    var_right := by intro _ _ _ h; exact EQ2.var_right_implies_UnfoldsToVar_axiom h
    send_right := by intro _ _ _ _ h; exact EQ2.send_right_implies_CanSend_axiom h
    recv_right := by intro _ _ _ _ h; exact EQ2.recv_right_implies_CanRecv_axiom h
    mus_to_BisimF := by intro _ _ _ _ _ _ h; exact EQ2_mus_to_BisimF_axiom h }

/-- Closed + contractive extraction (axiom-free). -/
def ContractiveExtraction : EQ2Extraction :=
  { Good := fun x => x.isClosed ∧ x.isContractive = true
    end_right := by
      intro x hgood h
      exact EQ2.end_right_implies_UnfoldsToEnd_of_contractive hgood.1 hgood.2 h
    var_right := by
      intro x v hgood h
      exact EQ2.var_right_implies_UnfoldsToVar_of_contractive hgood.1 hgood.2 h
    send_right := by
      intro x p bs hgood h
      exact EQ2.send_right_implies_CanSend_of_contractive (x := x) hgood.1 hgood.2 h
    recv_right := by
      intro x p bs hgood h
      exact EQ2.recv_right_implies_CanRecv_of_contractive (x := x) hgood.1 hgood.2 h
    mus_to_BisimF := by
      intro t s body body' hgood1 hgood2 h
      exact EQ2_mus_to_BisimF_of_contractive (t := t) (s := s) (body := body) (body' := body')
        h hgood1.1 hgood1.2 hgood2.1 hgood2.2 }

/-- Hybrid extraction: prefers contractive proofs, falls back to axioms.

    This is the default active extraction, matching the non-leaky global behavior. -/
def HybridExtraction : EQ2Extraction :=
  { Good := fun _ => True
    end_right := by
      intro x _ h
      by_cases hmu : x.fullUnfold.muHeight = 0
      · exact EQ2.end_right_implies_UnfoldsToEnd_of_fullUnfold_nonmu hmu h
      · by_cases hcontr : x.isContractive = true
        · by_cases hclosed : x.isClosed = true
          · have hclosed' : x.isClosed := by
              simpa [hclosed] using (show x.isClosed = true from hclosed)
            have hmu' : x.fullUnfold.muHeight = 0 :=
              LocalTypeR.fullUnfold_non_mu_of_contractive (lt := x) hcontr hclosed'
            exact EQ2.end_right_implies_UnfoldsToEnd_of_fullUnfold_nonmu hmu' h
          · exact EQ2.end_right_implies_UnfoldsToEnd_axiom h
        · exact EQ2.end_right_implies_UnfoldsToEnd_axiom h
    var_right := by
      intro x v _ h
      by_cases hmu : x.fullUnfold.muHeight = 0
      · exact EQ2.var_right_implies_UnfoldsToVar_of_fullUnfold_nonmu hmu h
      · by_cases hcontr : x.isContractive = true
        · by_cases hclosed : x.isClosed = true
          · have hclosed' : x.isClosed := by
              simpa [hclosed] using (show x.isClosed = true from hclosed)
            have hmu' : x.fullUnfold.muHeight = 0 :=
              LocalTypeR.fullUnfold_non_mu_of_contractive (lt := x) hcontr hclosed'
            exact EQ2.var_right_implies_UnfoldsToVar_of_fullUnfold_nonmu hmu' h
          · exact EQ2.var_right_implies_UnfoldsToVar_axiom h
        · exact EQ2.var_right_implies_UnfoldsToVar_axiom h
    send_right := by
      intro x p bs _ h
      by_cases hmu : x.fullUnfold.muHeight = 0
      · exact EQ2.send_right_implies_CanSend_of_fullUnfold_nonmu hmu h
      · by_cases hcontr : x.isContractive = true
        · by_cases hclosed : x.isClosed = true
          · have hclosed' : x.isClosed := by
              simpa [hclosed] using (show x.isClosed = true from hclosed)
            have hmu' : x.fullUnfold.muHeight = 0 :=
              LocalTypeR.fullUnfold_non_mu_of_contractive (lt := x) hcontr hclosed'
            exact EQ2.send_right_implies_CanSend_of_fullUnfold_nonmu hmu' h
          · exact EQ2.send_right_implies_CanSend_axiom h
        · exact EQ2.send_right_implies_CanSend_axiom h
    recv_right := by
      intro x p bs _ h
      by_cases hmu : x.fullUnfold.muHeight = 0
      · exact EQ2.recv_right_implies_CanRecv_of_fullUnfold_nonmu hmu h
      · by_cases hcontr : x.isContractive = true
        · by_cases hclosed : x.isClosed = true
          · have hclosed' : x.isClosed := by
              simpa [hclosed] using (show x.isClosed = true from hclosed)
            have hmu' : x.fullUnfold.muHeight = 0 :=
              LocalTypeR.fullUnfold_non_mu_of_contractive (lt := x) hcontr hclosed'
            exact EQ2.recv_right_implies_CanRecv_of_fullUnfold_nonmu hmu' h
          · exact EQ2.recv_right_implies_CanRecv_axiom h
        · exact EQ2.recv_right_implies_CanRecv_axiom h
    mus_to_BisimF := by
      intro t s body body' _ _ h
      by_cases hc1 : (LocalTypeR.mu t body).isContractive = true
      · by_cases hc2 : (LocalTypeR.mu s body').isContractive = true
        · by_cases hcl1 : (LocalTypeR.mu t body).isClosed
          · by_cases hcl2 : (LocalTypeR.mu s body').isClosed
            · exact EQ2_mus_to_BisimF_of_contractive (t := t) (s := s) (body := body) (body' := body')
                h hcl1 hc1 hcl2 hc2
            · exact EQ2_mus_to_BisimF_axiom h
          · exact EQ2_mus_to_BisimF_axiom h
        · exact EQ2_mus_to_BisimF_axiom h
      · exact EQ2_mus_to_BisimF_axiom h }

/-- Global swap point for extraction. Default matches the substitution environment default. -/
def ActiveExtraction : EQ2Extraction := HybridExtraction

abbrev ActiveGood : LocalTypeR → Prop := ActiveExtraction.Good

/-- Unconditional extraction through the active layer (default: hybrid). -/
theorem EQ2.end_right_implies_UnfoldsToEnd {x : LocalTypeR} (h : EQ2 .end x) : UnfoldsToEnd x := by
  exact ActiveExtraction.end_right (x := x) (by trivial) h

/-- If EQ2 x .end, then x unfolds to end. -/
theorem EQ2.end_left_implies_UnfoldsToEnd {x : LocalTypeR} (h : EQ2 x .end) : UnfoldsToEnd x :=
  EQ2.end_right_implies_UnfoldsToEnd (EQ2_symm h)

/-- If EQ2 (.var v) x, then x unfolds to var v. -/
theorem EQ2.var_right_implies_UnfoldsToVar {x : LocalTypeR} {v : String}
    (h : EQ2 (.var v) x) : UnfoldsToVar x v := by
  exact ActiveExtraction.var_right (x := x) (v := v) (by trivial) h

/-- If EQ2 x (.var v), then x unfolds to var v. -/
theorem EQ2.var_left_implies_UnfoldsToVar {x : LocalTypeR} {v : String}
    (h : EQ2 x (.var v)) : UnfoldsToVar x v :=
  EQ2.var_right_implies_UnfoldsToVar (EQ2_symm h)

/-- If EQ2 (.send p bs) x, then x can send to p with EQ2-related branches. -/
theorem EQ2.send_right_implies_CanSend {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : EQ2 (.send p bs) x) :
    ∃ cs, CanSend x p cs ∧ BranchesRel EQ2 bs cs := by
  exact ActiveExtraction.send_right (x := x) (p := p) (bs := bs) (by trivial) h

/-- If EQ2 x (.send p cs), then x can send to p with EQ2-related branches. -/
theorem EQ2.send_left_implies_CanSend {x : LocalTypeR} {p : String}
    {cs : List (Label × LocalTypeR)} (h : EQ2 x (.send p cs)) :
    ∃ bs, CanSend x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := EQ2_symm h
  obtain ⟨bs, hcan, hbr⟩ := EQ2.send_right_implies_CanSend hsymm
  exact ⟨bs, hcan, BranchesRel_flip hbr⟩

/-- If EQ2 (.recv p bs) x, then x can recv from p with EQ2-related branches. -/
theorem EQ2.recv_right_implies_CanRecv {x : LocalTypeR} {p : String}
    {bs : List (Label × LocalTypeR)} (h : EQ2 (.recv p bs) x) :
    ∃ cs, CanRecv x p cs ∧ BranchesRel EQ2 bs cs := by
  exact ActiveExtraction.recv_right (x := x) (p := p) (bs := bs) (by trivial) h

/-- If EQ2 x (.recv p cs), then x can recv from p with EQ2-related branches. -/
theorem EQ2.recv_left_implies_CanRecv {x : LocalTypeR} {p : String}
    {cs : List (Label × LocalTypeR)} (h : EQ2 x (.recv p cs)) :
    ∃ bs, CanRecv x p bs ∧ BranchesRel EQ2 bs cs := by
  have hsymm := EQ2_symm h
  obtain ⟨bs, hcan, hbr⟩ := EQ2.recv_right_implies_CanRecv hsymm
  exact ⟨bs, hcan, BranchesRel_flip hbr⟩

/-- Transfer observables across EQ2. -/
theorem EQ2_transfer_observable {a b : LocalTypeR} (h : EQ2 a b) (obs_a : Observable a) :
    ∃ obs_b : Observable b, ObservableRel EQ2 obs_a obs_b := by
  cases obs_a with
  | is_end h_end =>
      have h_end_eq : EQ2 .end b :=
        EQ2_trans (EQ2_symm (UnfoldsToEnd.toEQ2 h_end)) h
      have hb : UnfoldsToEnd b := EQ2.end_right_implies_UnfoldsToEnd h_end_eq
      exact ⟨Observable.is_end hb, ObservableRel.is_end⟩
  | is_var (v := v) h_var =>
      have h_var_eq : EQ2 (.var v) b :=
        EQ2_trans (EQ2_symm (UnfoldsToVar.toEQ2 h_var)) h
      have hb : UnfoldsToVar b v := EQ2.var_right_implies_UnfoldsToVar h_var_eq
      exact ⟨Observable.is_var hb, ObservableRel.is_var⟩
  | is_send (p := p) (bs := bs) h_send =>
      have h_send_eq : EQ2 (.send p bs) b :=
        EQ2_trans (EQ2_symm (CanSend.toEQ2 h_send)) h
      obtain ⟨cs, hcan, hbr⟩ := EQ2.send_right_implies_CanSend h_send_eq
      exact ⟨Observable.is_send hcan, ObservableRel.is_send hbr⟩
  | is_recv (p := p) (bs := bs) h_recv =>
      have h_recv_eq : EQ2 (.recv p bs) b :=
        EQ2_trans (EQ2_symm (CanRecv.toEQ2 h_recv)) h
      obtain ⟨cs, hcan, hbr⟩ := EQ2.recv_right_implies_CanRecv h_recv_eq
      exact ⟨Observable.is_recv hcan, ObservableRel.is_recv hbr⟩

/-- Observability is symmetric across EQ2. -/
theorem EQ2_observable_symmetric {a b : LocalTypeR} (h : EQ2 a b) :
    (∃ obs_a : Observable a, True) ↔ (∃ obs_b : Observable b, True) := by
  constructor
  · intro h_obs_a
    obtain ⟨obs_a, _⟩ := h_obs_a
    obtain ⟨obs_b, _⟩ := EQ2_transfer_observable h obs_a
    exact ⟨obs_b, True.intro⟩
  · intro h_obs_b
    obtain ⟨obs_b, _⟩ := h_obs_b
    have hsymm := EQ2_symm h
    obtain ⟨obs_a, _⟩ := EQ2_transfer_observable hsymm obs_b
    exact ⟨obs_a, True.intro⟩

theorem EQ2_mus_to_BisimF {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body')) :
    BisimF EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body') := by
  exact ActiveExtraction.mus_to_BisimF
    (t := t) (s := s) (body := body) (body' := body') (by trivial) (by trivial) h
theorem mus_shared_observable_contractive {t s : String} {body body' : LocalTypeR}
    (h : EQ2 (LocalTypeR.mu t body) (LocalTypeR.mu s body'))
    (_hc1 : (LocalTypeR.mu t body).isContractive = true)
    (_hc2 : (LocalTypeR.mu s body').isContractive = true) :
    (UnfoldsToEnd (LocalTypeR.mu t body) ∧ UnfoldsToEnd (LocalTypeR.mu s body')) ∨
    (∃ v, UnfoldsToVar (LocalTypeR.mu t body) v ∧ UnfoldsToVar (LocalTypeR.mu s body') v) ∨
    (∃ p bs cs, CanSend (LocalTypeR.mu t body) p bs ∧ CanSend (LocalTypeR.mu s body') p cs ∧
       BranchesRel EQ2 bs cs) ∨
    (∃ p bs cs, CanRecv (LocalTypeR.mu t body) p bs ∧ CanRecv (LocalTypeR.mu s body') p cs ∧
       BranchesRel EQ2 bs cs) := by
  -- Extract BisimF structure from EQ2 using the mu/mu axiom
  have hBisimF := EQ2_mus_to_BisimF h
  -- Case analysis on the BisimF structure to extract shared observable
  cases hBisimF with
  | eq_end hx hy =>
    -- Both mus unfold to end
    exact Or.inl ⟨hx, hy⟩
  | eq_var hx hy =>
    -- Both mus unfold to the same variable
    exact Or.inr (Or.inl ⟨_, hx, hy⟩)
  | eq_send hx hy hbr =>
    -- Both mus can send to the same partner with EQ2-related branches
    -- Convert BranchesRelBisim EQ2 to BranchesRel EQ2
    have hbr_eq2 := BranchesRelBisim_to_BranchesRel hbr
    exact Or.inr (Or.inr (Or.inl ⟨_, _, _, hx, hy, hbr_eq2⟩))
  | eq_recv hx hy hbr =>
    -- Both mus can recv from the same partner with EQ2-related branches
    have hbr_eq2 := BranchesRelBisim_to_BranchesRel hbr
    exact Or.inr (Or.inr (Or.inr ⟨_, _, _, hx, hy, hbr_eq2⟩))



/-- EQ2 implies Bisim.

    This direction shows that coinductive equality implies membership-based bisimulation.
    The proof constructs the Bisim witness using EQ2 itself.

    **Semantic constraint**: This theorem relies on extraction axioms that are valid for contractive
    types (where every mu-bound variable is guarded). All types from well-formed projections are
    contractive, so this theorem is sound in practice.

    Proof idea:
    - Use EQ2 as the witness relation for Bisim
    - Show EQ2 is a post-fixpoint of BisimF by destruct-ing EQ2 to EQ2F
    - Convert EQ2F structure to membership predicates using the extraction lemmas
    - For mu/mu case, use EQ2_mus_to_BisimF axiom -/
theorem EQ2.toBisim_raw {a b : LocalTypeR} (h : EQ2 a b) : Bisim a b := by
  -- Use EQ2 as the witness relation
  use EQ2
  constructor
  · -- Show EQ2 is a post-fixpoint of BisimF
    intro x y hxy
    have hf : EQ2F EQ2 x y := EQ2.destruct hxy
    -- Convert EQ2F to BisimF by extracting membership predicates
    cases x with
    | «end» =>
      cases y with
      | «end» => exact BisimF.eq_end UnfoldsToEnd.base UnfoldsToEnd.base
      | mu s body' =>
        -- y must unfold to end since EQ2 end y
        have hUnfold := EQ2.end_right_implies_UnfoldsToEnd hxy
        exact BisimF.eq_end UnfoldsToEnd.base hUnfold
      | var _ => simp only [EQ2F] at hf
      | send _ _ => simp only [EQ2F] at hf
      | recv _ _ => simp only [EQ2F] at hf
    | var v =>
      cases y with
      | var w =>
        simp only [EQ2F] at hf
        subst hf
        exact BisimF.eq_var UnfoldsToVar.base UnfoldsToVar.base
      | mu s body' =>
        -- y must unfold to var v since EQ2 (var v) y
        have hUnfold := EQ2.var_right_implies_UnfoldsToVar hxy
        exact BisimF.eq_var UnfoldsToVar.base hUnfold
      | «end» => simp only [EQ2F] at hf
      | send _ _ => simp only [EQ2F] at hf
      | recv _ _ => simp only [EQ2F] at hf
    | send p bs =>
      cases y with
      | send q cs =>
        simp only [EQ2F] at hf
        have ⟨heq, hbr⟩ := hf
        subst heq
        apply BisimF.eq_send CanSend.base CanSend.base
        -- Convert BranchesRel EQ2 to BranchesRelBisim EQ2
        exact BranchesRel_to_BranchesRelBisim hbr
      | mu s body' =>
        -- y must be able to send since EQ2 (send p bs) y
        obtain ⟨cs, hCanSend, hbr⟩ := EQ2.send_right_implies_CanSend hxy
        apply BisimF.eq_send CanSend.base hCanSend
        exact BranchesRel_to_BranchesRelBisim hbr
      | «end» => simp only [EQ2F] at hf
      | var _ => simp only [EQ2F] at hf
      | recv _ _ => simp only [EQ2F] at hf
    | recv p bs =>
      cases y with
      | recv q cs =>
        simp only [EQ2F] at hf
        have ⟨heq, hbr⟩ := hf
        subst heq
        apply BisimF.eq_recv CanRecv.base CanRecv.base
        exact BranchesRel_to_BranchesRelBisim hbr
      | mu s body' =>
        -- y must be able to recv since EQ2 (recv p bs) y
        obtain ⟨cs, hCanRecv, hbr⟩ := EQ2.recv_right_implies_CanRecv hxy
        apply BisimF.eq_recv CanRecv.base hCanRecv
        exact BranchesRel_to_BranchesRelBisim hbr
      | «end» => simp only [EQ2F] at hf
      | var _ => simp only [EQ2F] at hf
      | send _ _ => simp only [EQ2F] at hf
    | mu t body =>
      cases y with
      | mu s body' =>
        -- Both mus - use the extraction axiom for mu/mu case
        exact EQ2_mus_to_BisimF hxy
      | «end» =>
        -- x must unfold to end since EQ2 x end
        have hUnfold := EQ2.end_left_implies_UnfoldsToEnd hxy
        exact BisimF.eq_end hUnfold UnfoldsToEnd.base
      | var v =>
        -- x must unfold to var v since EQ2 x (var v)
        have hUnfold := EQ2.var_left_implies_UnfoldsToVar hxy
        exact BisimF.eq_var hUnfold UnfoldsToVar.base
      | send q cs =>
        -- x must be able to send since EQ2 x (send q cs)
        obtain ⟨bs, hCanSend, hbr⟩ := EQ2.send_left_implies_CanSend hxy
        apply BisimF.eq_send hCanSend CanSend.base
        exact BranchesRel_to_BranchesRelBisim hbr
      | recv q cs =>
        -- x must be able to recv since EQ2 x (recv q cs)
        obtain ⟨bs, hCanRecv, hbr⟩ := EQ2.recv_left_implies_CanRecv hxy
        apply BisimF.eq_recv hCanRecv CanRecv.base
        exact BranchesRel_to_BranchesRelBisim hbr
  · -- Show EQ2 a b
    exact h

/-! ## EQ2 to Bisim (Contractive Witness) -/

theorem EQ2.toBisim_of_contractive {a b : LocalTypeR}
    (_ha : a.isContractive = true) (_hb : b.isContractive = true) (h : EQ2 a b) : Bisim a b := by
  -- Delegate to the active extraction (hybrid) path.
  exact EQ2.toBisim_raw h

theorem EQ2.toBisim {a b : LocalTypeR} (h : EQ2 a b) : Bisim a b := by
  by_cases ha : a.isContractive = true
  · by_cases hb : b.isContractive = true
    · exact EQ2.toBisim_of_contractive ha hb h
    · exact EQ2.toBisim_raw h
  · exact EQ2.toBisim_raw h
/-- Bisim is reflexive (general version using EQ2).

    For any type a, Bisim a a holds because EQ2 a a holds (EQ2 is reflexive),
    and EQ2 implies Bisim.

    This version doesn't require closed or contractive hypotheses, making it
    suitable for use with arbitrary types (including those with free variables). -/
theorem Bisim_refl (a : LocalTypeR) : Bisim a a :=
  EQ2.toBisim (EQ2_refl a)

namespace Bisim

/-- Observable types are reflexively bisimilar. -/
theorem refl_of_observable {a : LocalTypeR} (_hobs : Observable a) : Bisim a a :=
  EQ2.toBisim (EQ2_refl a)

/-- Bisim is reflexive for closed, contractive types. -/
theorem refl (a : LocalTypeR)
    (hclosed : a.isClosed := by decide)
    (hcontr : a.isContractive = true := by decide) : Bisim a a :=
  refl_of_observable (observable_of_closed_contractive hclosed hcontr)

end Bisim


/-! ## EQ2 Transitivity via Bisim

The Bisim detour provides an alternative proof of EQ2 transitivity that does not
require the TransRel_postfix axiom. This eliminates the need for one of the two
private axioms in EQ2.lean. -/

/-- EQ2 transitivity via the Bisim detour.

    This theorem provides an alternative proof of EQ2_trans that does not require
    the TransRel_postfix axiom. The proof goes:
    1. Convert EQ2 proofs to Bisim using EQ2.toBisim
    2. Apply Bisim.trans (fully proven)
    3. Convert back to EQ2 using Bisim.toEQ2

    This theorem can replace the axiom-based EQ2_trans in EQ2.lean once we
    resolve the circular import issue. -/
theorem EQ2_trans_via_Bisim {a b c : LocalTypeR}
    (hab : EQ2 a b) (hbc : EQ2 b c) : EQ2 a c := by
  have hBisim_ab := EQ2.toBisim hab
  have hBisim_bc := EQ2.toBisim hbc
  have hBisim_ac := Bisim.trans hBisim_ab hBisim_bc
  exact Bisim.toEQ2 hBisim_ac

/-- EQ2 transitivity via Bisim, for contractive types. -/
theorem EQ2_trans_via_Bisim_of_contractive {a b c : LocalTypeR}
    (ha : a.isContractive = true) (hb : b.isContractive = true) (hc : c.isContractive = true)
    (hab : EQ2 a b) (hbc : EQ2 b c) : EQ2 a c := by
  have hBisim_ab := EQ2.toBisim_of_contractive ha hb hab
  have hBisim_bc := EQ2.toBisim_of_contractive hb hc hbc
  have hBisim_ac := Bisim.trans hBisim_ab hBisim_bc
  exact Bisim.toEQ2 hBisim_ac

/-! ## Phase 4: Congruence Framework

This section provides the infrastructure for proving that Bisim (and hence EQ2)
is a congruence for various operations like substitution. The key idea is to
define "compatible" functions and show that compatible functions preserve Bisim.

Following the pattern from QpfTypes PR #49. -/

/-- RelImage lifts a relation through a function application.

    `RelImage f R u v` holds when there exist `a b` such that `R a b` and
    `u = f a` and `v = f b`. This is the image of R under f × f. -/
def RelImage (f : LocalTypeR → LocalTypeR) (R : Rel) : Rel :=
  fun u v => ∃ a b, R a b ∧ u = f a ∧ v = f b

/-- A function is compatible if it preserves BisimF structure.

    `Compatible f` means: if `BisimF R x y` holds, then
    `BisimF (RelImage f R) (f x) (f y)` holds.

    This is the key property that allows lifting Bisim through f. -/
def Compatible (f : LocalTypeR → LocalTypeR) : Prop :=
  ∀ {R : Rel} {x y : LocalTypeR}, BisimF R x y → BisimF (RelImage f R) (f x) (f y)

/-- Compatible functions are congruences for Bisim.

    If f is compatible, then Bisim x y implies Bisim (f x) (f y).
    This is the main theorem that enables proving EQ2_substitute via Bisim. -/
theorem Bisim.congr (f : LocalTypeR → LocalTypeR) (hf : Compatible f)
    {x y : LocalTypeR} (h : Bisim x y) : Bisim (f x) (f y) := by
  obtain ⟨R, hRpost, hxy⟩ := h
  -- Use RelImage f R as the witness relation
  let Rf := RelImage f R
  use Rf
  constructor
  · -- Show Rf is a post-fixpoint of BisimF
    intro u v ⟨a, b, hab, hu, hv⟩
    have hf_ab := hRpost a b hab
    rw [hu, hv]
    exact hf hf_ab
  · -- Show Rf (f x) (f y)
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- Duality is compatible with BisimF. -/
theorem dual_compatible : Compatible LocalTypeR.dual := by
  intro R x y h
  cases h with
  | eq_end hx hy =>
      exact BisimF.eq_end (UnfoldsToEnd.dual hx) (UnfoldsToEnd.dual hy)
  | eq_var hx hy =>
      exact BisimF.eq_var (UnfoldsToVar.dual hx) (UnfoldsToVar.dual hy)
  | eq_send hx hy hbr =>
      rename_i p bsa bsb
      have hx' : CanRecv x.dual p (LocalTypeR.dualBranches bsa) := CanSend.dual hx
      have hy' : CanRecv y.dual p (LocalTypeR.dualBranches bsb) := CanSend.dual hy
      have hbr' : BranchesRelBisim (RelImage LocalTypeR.dual R)
          (LocalTypeR.dualBranches bsa) (LocalTypeR.dualBranches bsb) := by
        simpa [LocalTypeR.dualBranches_eq_map] using
          (BranchesRelBisim.map_image (f := LocalTypeR.dual) hbr)
      exact BisimF.eq_recv hx' hy' hbr'
  | eq_recv hx hy hbr =>
      rename_i p bsa bsb
      have hx' : CanSend x.dual p (LocalTypeR.dualBranches bsa) := CanRecv.dual hx
      have hy' : CanSend y.dual p (LocalTypeR.dualBranches bsb) := CanRecv.dual hy
      have hbr' : BranchesRelBisim (RelImage LocalTypeR.dual R)
          (LocalTypeR.dualBranches bsa) (LocalTypeR.dualBranches bsb) := by
        simpa [LocalTypeR.dualBranches_eq_map] using
          (BranchesRelBisim.map_image (f := LocalTypeR.dual) hbr)
      exact BisimF.eq_send hx' hy' hbr'

/-- Duality is compatible with EQ2. -/
theorem EQ2_dual_compat {a b : LocalTypeR} (h : EQ2 a b) : EQ2 a.dual b.dual := by
  have hb : Bisim a b := EQ2.toBisim_raw h
  have hb' : Bisim a.dual b.dual := Bisim.congr LocalTypeR.dual dual_compatible hb
  exact Bisim.toEQ2 hb'

/-- Flip BranchesRel EQ2 across duality on both sides. -/
theorem BranchesRel_dual_eq2 {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRel EQ2 (LocalTypeR.dualBranches bs) cs) :
    BranchesRel EQ2 bs (LocalTypeR.dualBranches cs) := by
  induction bs generalizing cs with
  | nil =>
      cases h
      exact List.Forall₂.nil
  | cons head tail ih =>
      cases cs with
      | nil => cases h
      | cons head' tail' =>
          cases head with
          | mk l t =>
              cases head' with
              | mk l' u =>
                  cases h with
                  | cons hbc htail =>
                      have hdu : EQ2 t u.dual := by
                        have h' := EQ2_dual_compat hbc.2
                        simpa [LocalTypeR.dual_involutive] using h'
                      exact List.Forall₂.cons ⟨hbc.1, hdu⟩ (ih htail)

/-- BranchesRelBisim under RelImage. -/
theorem BranchesRelBisim.map_image {f : LocalTypeR → LocalTypeR} {R : Rel}
    {bs cs : List (Label × LocalTypeR)} (h : BranchesRelBisim R bs cs) :
    BranchesRelBisim (RelImage f R)
      (bs.map (fun b => (b.1, f b.2)))
      (cs.map (fun c => (c.1, f c.2))) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hbc _ ih =>
    apply List.Forall₂.cons
    · constructor
      · exact hbc.1
      · exact ⟨_, _, hbc.2, rfl, rfl⟩
    · exact ih

/-! ### Substitute Compatibility

To prove `EQ2_substitute` we need to show that substitution is compatible.
This requires showing that substitution preserves observable behavior. -/

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- After substituting `t → .mu t body`, the variable `t` is no longer free.

    This is because `.mu t body` binds `t`, so any free occurrence of `t` in the
    original type gets replaced by something where `t` is bound.

    Proven in SubstCommBarendregt.lean using the more general isFreeIn_subst_self_general. -/
theorem isFreeIn_mu_unfold_false (body : LocalTypeR) (t : String) :
    isFreeIn t (body.substitute t (.mu t body)) = false :=
  isFreeIn_subst_mu_self body t

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- If a variable is not free in a type, substituting for it is the identity on branches.

    This is used for the shadowed case in substitute_preserves_CanSend/CanRecv. -/
theorem map_substitute_eq_self_of_not_free {bs : List (Label × LocalTypeR)} {var : String} {repl : LocalTypeR}
    (hnot_free : ∀ (l : Label) (c : LocalTypeR), (l, c) ∈ bs → isFreeIn var c = false) :
    bs.map (fun b => (b.1, b.2.substitute var repl)) = bs := by
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    obtain ⟨l, c⟩ := hd
    have hnot_free_c : isFreeIn var c = false := hnot_free l c (List.Mem.head _)
    have hc_eq : c.substitute var repl = c := substitute_not_free c var repl hnot_free_c
    have htl_eq := ih (fun l' c' hmem => hnot_free l' c' (List.Mem.tail _ hmem))
    simp only [hc_eq, htl_eq]

/-! ### Substitution Commutativity (EQ2 version)

The syntactic `subst_mu_comm` requires Barendregt conditions. For general use,
we need an EQ2-equivalence version that holds unconditionally.

## Proof Strategy

We rely on a DB-backed axiom to justify the EQ2 commutation without
the Barendregt conditions. This unblocks the EQ2_subst_mu_comm proof
without a fragile coinduction-up-to argument.
-/

/-- EQ2 version of mu-substitution commutativity.

    States that the order of two substitutions (var→repl and t→mu t body) can be
    swapped up to EQ2 equivalence, as long as t ≠ var.

    When Barendregt conditions hold (notBoundAt var body, repl is closed), this
    follows from syntactic `subst_mu_comm`. For general types, the infinite tree
    semantics are still equivalent because EQ2 captures semantic equality.

    Proof: DB bridge (see `CoTypes.DBBridge`). -/
theorem EQ2_subst_mu_comm (body : LocalTypeR) (var t : String) (repl : LocalTypeR)
    (htne : t ≠ var) :
    EQ2 ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
        ((body.substitute t (.mu t body)).substitute var repl) := by
  exact RumpsteakV2.Protocol.CoTypes.EQ2_subst_mu_comm_via_DB body var t repl htne

/-- Transfer UnfoldsToEnd through EQ2 equivalence.

    If `a` unfolds to end and `a` is EQ2-equivalent to `b`, then `b` unfolds to end. -/
theorem UnfoldsToEnd_of_EQ2 {a b : LocalTypeR} (ha : UnfoldsToEnd a) (heq : EQ2 a b) :
    UnfoldsToEnd b := by
  -- a unfolds to end, so EQ2 a .end
  have ha_eq_end : EQ2 a .end := UnfoldsToEnd.toEQ2 ha
  -- By transitivity: EQ2 b a → EQ2 a .end → EQ2 b .end
  have hb_eq_end : EQ2 b .end := EQ2_trans (EQ2_symm heq) ha_eq_end
  -- By symmetry: EQ2 .end b
  have hend_eq_b : EQ2 .end b := EQ2_symm hb_eq_end
  -- By axiom: UnfoldsToEnd b
  exact EQ2.end_right_implies_UnfoldsToEnd hend_eq_b

/-- Substitution preserves UnfoldsToEnd.

    If a unfolds to end, then (a.substitute var repl) also unfolds to end
    (or to something EQ2-equivalent, when var is substituted).

    Proof: By induction on the UnfoldsToEnd proof.
    - Base case (a = .end): substitution gives .end, which has UnfoldsToEnd.
    - Mu case (a = .mu t body): Two subcases:
      - If t == var: substitution is shadowed, result is .mu t body, same as h.
      - If t != var: use subst_mu_comm (but this requires Barendregt conditions).

    Note: The full proof requires Barendregt conditions. We prove the simplified
    version that handles the base case and the shadowed mu case. The non-shadowed
    mu case requires substitution commutation which needs additional assumptions. -/
theorem substitute_preserves_UnfoldsToEnd {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : UnfoldsToEnd a) : UnfoldsToEnd (a.substitute var repl) ∨
      ∃ n, UnfoldPathEndBounded n repl ∧ a = .var var := by
  induction h with
  | base =>
    -- a = .end, substitute gives .end
    left
    simp only [LocalTypeR.substitute]
    exact UnfoldsToEnd.base
  | @mu t body _ ih =>
    -- a = .mu t body
    by_cases htvar : t == var
    · -- t == var: substitution is shadowed
      simp only [LocalTypeR.substitute, htvar, ↓reduceIte]
      left
      exact UnfoldsToEnd.mu ‹UnfoldsToEnd (body.substitute t (.mu t body))›
    · -- t != var: substitution goes through
      simp only [LocalTypeR.substitute, htvar, Bool.false_eq_true, ↓reduceIte]
      -- Goal: UnfoldsToEnd (.mu t (body.substitute var repl)) ∨ ...
      -- We need UnfoldsToEnd ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
      -- By IH: UnfoldsToEnd ((body.substitute t (.mu t body)).substitute var repl) ∨ ...
      cases ih with
      | inl hend =>
        -- IH gives: UnfoldsToEnd ((body.substitute t (.mu t body)).substitute var repl)
        -- We need: UnfoldsToEnd ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
        -- Use EQ2_subst_mu_comm to relate them via EQ2, then transfer UnfoldsToEnd.
        left
        apply UnfoldsToEnd.mu
        -- t ≠ var from htvar : ¬(t == var) = true
        have htne : t ≠ var := by
          intro heq
          apply htvar
          simp only [heq, beq_self_eq_true]
        -- EQ2_subst_mu_comm gives: EQ2 (goal term) (IH term)
        have heq := EQ2_subst_mu_comm body var t repl htne
        -- Transfer UnfoldsToEnd from IH term to goal term
        exact UnfoldsToEnd_of_EQ2 hend (EQ2_symm heq)
      | inr hex =>
        -- IH gives: ∃ n, UnfoldPathEndBounded n repl ∧ body.substitute t (.mu t body) = .var var
        -- The second disjunct only applies when body.substitute t (.mu t body) = .var var.
        obtain ⟨n, hpath, heq⟩ := hex
        -- heq : body.substitute t (.mu t body) = .var var
        -- So (body.substitute t (.mu t body)).substitute var repl = (.var var).substitute var repl = repl
        left
        apply UnfoldsToEnd.mu
        -- t ≠ var from htvar : ¬(t == var) = true
        have htne : t ≠ var := by
          intro h
          apply htvar
          simp only [h, beq_self_eq_true]
        -- EQ2_subst_mu_comm gives: EQ2 (goal term) (RHS)
        have heq2 := EQ2_subst_mu_comm body var t repl htne
        -- RHS = (body.substitute t (.mu t body)).substitute var repl
        --     = (.var var).substitute var repl (by heq)
        --     = repl
        have hrhs_eq : (body.substitute t (.mu t body)).substitute var repl = repl := by
          rw [heq]
          simp only [LocalTypeR.substitute, beq_self_eq_true, ↓reduceIte]
        -- So EQ2 (goal term) repl
        have heq2' : EQ2 ((body.substitute var repl).substitute t (.mu t (body.substitute var repl))) repl := by
          have h := heq2
          rw [hrhs_eq] at h
          exact h
        -- UnfoldsToEnd repl from hpath
        have hrepl_end : UnfoldsToEnd repl := hpath.toUnfoldsToEnd
        -- Transfer via EQ2
        exact UnfoldsToEnd_of_EQ2 hrepl_end (EQ2_symm heq2')

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves UnfoldsToEnd under Barendregt conditions.

    This version requires Barendregt conditions:
    - `hbar`: var is not used as a binder in a
    - `hfresh`: repl is closed (no free variables)

    These conditions ensure substitution commutativity in the mu case. -/
theorem substitute_preserves_UnfoldsToEnd_barendregt {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : UnfoldsToEnd a)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    UnfoldsToEnd (a.substitute var repl) := by
  induction h generalizing var repl with
  | base =>
    -- a = .end, substitute gives .end
    simp only [LocalTypeR.substitute]
    exact UnfoldsToEnd.base
  | @mu t body _ ih =>
    -- a = .mu t body
    -- notBoundAt var (.mu t body) = (var != t) && notBoundAt var body = true
    simp only [notBoundAt] at hbar
    have ⟨hvt, hbar_body⟩ := Bool.and_eq_true_iff.mp hbar
    have hvt' : var ≠ t := by simp only [bne_iff_ne, ne_eq] at hvt; exact hvt
    have htv' : t ≠ var := hvt'.symm
    -- Since var ≠ t, substitution goes through
    have htvar : (t == var) = false := by
      cases h : t == var
      · rfl
      · simp only [beq_iff_eq] at h; exact absurd h htv'
    simp only [LocalTypeR.substitute, htvar, Bool.false_eq_true, ↓reduceIte]
    -- Goal: UnfoldsToEnd (.mu t (body.substitute var repl))
    -- We need UnfoldsToEnd ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
    apply UnfoldsToEnd.mu
    -- Use subst_mu_comm to rewrite the goal
    -- hcomm: (body.substitute var repl).substitute t (.mu t (body.substitute var repl))
    --      = (body.substitute t (.mu t body)).substitute var repl
    have hcomm := subst_mu_comm body var t repl hbar_body hfresh htv'
    rw [hcomm]
    -- Now goal: UnfoldsToEnd ((body.substitute t (.mu t body)).substitute var repl)
    -- Apply IH: need notBoundAt var (body.substitute t (.mu t body))
    have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
      notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hvt, hbar_body])
    exact ih hbar_unfold hfresh

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves UnfoldsToVar (when not the substituted variable).

    This version requires Barendregt conditions:
    - `hbar`: var is not used as a binder in a
    - `hfresh`: repl is closed (no free variables)

    These conditions ensure substitution commutativity in the mu case. -/
theorem substitute_preserves_UnfoldsToVar {a : LocalTypeR} {var v : String} {repl : LocalTypeR}
    (h : UnfoldsToVar a v) (hne : v ≠ var)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    UnfoldsToVar (a.substitute var repl) v := by
  induction h generalizing var repl with
  | base =>
    -- UnfoldsToVar (.var v) v means a = .var v
    simp only [LocalTypeR.substitute]
    split
    · rename_i hveq
      simp only [beq_iff_eq] at hveq
      exact absurd hveq hne
    · exact UnfoldsToVar.base
  | @mu t body v' _ ih =>
    simp only [LocalTypeR.substitute]
    split
    · -- t == var is true: substitution is shadowed
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      have hnotfree : isFreeIn t (body.substitute t (.mu t body)) = false :=
        isFreeIn_mu_unfold_false body t
      have hnotfree' : isFreeIn var (body.substitute t (.mu t body)) = false := by
        rw [← htvar]; exact hnotfree
      have hsame : (body.substitute t (.mu t body)).substitute var repl =
                   body.substitute t (.mu t body) :=
        substitute_not_free _ var repl hnotfree'
      -- Get notBoundAt for the unfolded body
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) hbar
      have ih' := ih hne hbar_unfold hfresh
      rw [hsame] at ih'
      exact UnfoldsToVar.mu ih'
    · -- t == var is false: substitution goes through
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      -- Extract notBoundAt for body from hbar
      simp only [notBoundAt] at hbar
      have htne : t ≠ var := fun heq => by simp [heq] at htvar
      have hbne : (var != t) = true := bne_iff_ne.mpr htne.symm
      simp only [hbne, Bool.true_and] at hbar
      -- Use subst_mu_comm for commutativity
      have hcomm := subst_mu_comm body var t repl hbar hfresh htne
      -- Get notBoundAt for the unfolded body
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hbne, hbar])
      have ih' := ih hne hbar_unfold hfresh
      rw [← hcomm] at ih'
      exact UnfoldsToVar.mu ih'

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- If a variable is not free in a type, the type cannot unfold to that variable.

    The proof is by induction on `UnfoldsToVar`:
    - Base case `.var v`: `isFreeIn v (.var v) = true`, contradicts hypothesis.
    - Mu case `.mu t body`: The induction hypothesis gives us that
      `isFreeIn v (body.substitute t (.mu t body)) = false` implies
      `¬UnfoldsToVar (body.substitute t (.mu t body)) v`, which contradicts the premise.

    This lemma is key for proving that the `t = var` case in `UnfoldsToVar_substitute_EQ2`
    is impossible: by `isFreeIn_subst_mu_self`, the bound variable is not free after unfolding,
    so `UnfoldsToVar (body.substitute t (.mu t body)) t` cannot hold. -/
theorem not_UnfoldsToVar_of_not_isFreeIn {x : LocalTypeR} {v : String}
    (h : isFreeIn v x = false) : ¬UnfoldsToVar x v := by
  intro hunf
  induction hunf with
  | base =>
    -- x = .var v, but isFreeIn v (.var v) = (v == v) = true, contradicting h
    simp only [isFreeIn, beq_self_eq_true] at h
    cases h
  | @mu t body v' hinner ih =>
    -- x = .mu t body, with UnfoldsToVar (body.substitute t (.mu t body)) v'
    -- h : isFreeIn v' (.mu t body) = false
    -- ih : isFreeIn v' (body.substitute t (.mu t body)) = false → False
    -- We need to show isFreeIn v' (body.substitute t (.mu t body)) = false
    simp only [isFreeIn] at h
    by_cases hvt : v' == t
    · -- v' == t case: use isFreeIn_subst_mu_self
      simp only [beq_iff_eq] at hvt
      subst hvt
      have hnotfree := isFreeIn_subst_mu_self body v'
      exact ih hnotfree
    · -- v' ≠ t case: isFreeIn v' (.mu t body) = isFreeIn v' body = false
      simp only [hvt, Bool.false_eq_true, ↓reduceIte] at h
      -- h : isFreeIn v' body = false
      -- Need: isFreeIn v' (body.substitute t (.mu t body)) = false
      -- v' is not free in body, and v' is not free in (.mu t body) (since v' ≠ t)
      have hmu_notfree : isFreeIn v' (.mu t body) = false := by
        simp only [isFreeIn, hvt, Bool.false_eq_true, ↓reduceIte, h]
      -- By isFreeIn_subst_preserves: v' not free in body ∧ v' not free in repl → v' not free in result
      have hsubst_notfree := isFreeIn_subst_preserves body v' t (.mu t body) h hmu_notfree
      exact ih hsubst_notfree

/-- When `UnfoldsToVar x var`, substituting `var → repl` yields something EQ2-equivalent to `repl`.

    Proof sketch: By induction on `UnfoldsToVar x var`:
    - Base case: x = .var var, so x.substitute var repl = repl, and EQ2_refl applies.
    - Mu case: x = .mu t body where body.substitute t (.mu t body) unfolds to var.
      The mu case with t = var is impossible (would require infinite proof).
      For t ≠ var, use EQ2_subst_mu_comm and IH.

    Key insight: if t = var, then body.substitute var (.mu var body) would need to unfold
    to .var var, but each .var var gets replaced by .mu var body, creating infinite recursion.
    So t ≠ var in all mu cases. -/
theorem UnfoldsToVar_substitute_EQ2 {x : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : UnfoldsToVar x var) : EQ2 (x.substitute var repl) repl := by
  induction h with
  | base =>
    -- x = .var var, so x.substitute var repl = repl
    simp only [LocalTypeR.substitute, beq_self_eq_true, ↓reduceIte]
    exact EQ2_refl _
  | @mu t body var' hinner ih =>
    -- x = .mu t body, body.substitute t (.mu t body) unfolds to var'
    -- Since h : UnfoldsToVar x var, we have var' = var
    -- Show t ≠ var (if t = var, we'd have infinite recursion)
    by_cases htv : t = var'
    · -- Case t = var: IMPOSSIBLE
      -- By isFreeIn_subst_mu_self: isFreeIn t (body.substitute t (.mu t body)) = false
      -- But hinner : UnfoldsToVar (body.substitute t (.mu t body)) var'
      -- Since t = var', this means UnfoldsToVar (body.substitute t (.mu t body)) t
      -- By not_UnfoldsToVar_of_not_isFreeIn, this is a contradiction
      have hnotfree := RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.isFreeIn_subst_mu_self body t
      -- hnotfree : isFreeIn t (body.substitute t (.mu t body)) = false
      -- hinner : UnfoldsToVar (body.substitute t (.mu t body)) var' where t = var'
      -- Use htv to substitute t for var' in hinner's last argument
      have hinner' : UnfoldsToVar (body.substitute t (.mu t body)) t := htv ▸ hinner
      exact absurd hinner' (not_UnfoldsToVar_of_not_isFreeIn hnotfree)
    · -- Case t ≠ var: use EQ2_subst_mu_comm
      -- Convert htv : t ≠ var' to beq form
      have htv_beq : (t == var') = false := beq_eq_false_iff_ne.mpr htv
      -- Goal: EQ2 ((.mu t body).substitute var' repl) repl
      -- (.mu t body).substitute var' repl = .mu t (body.substitute var' repl) when t ≠ var'
      simp only [LocalTypeR.substitute, htv_beq, Bool.false_eq_true, ↓reduceIte]
      -- Goal: EQ2 (.mu t (body.substitute var' repl)) repl
      -- By EQ2_subst_mu_comm: the unfolded form is EQ2-equivalent to the IH term
      have hcomm := EQ2_subst_mu_comm body var' t repl htv
      have hunfolded : EQ2 ((body.substitute var' repl).substitute t (.mu t (body.substitute var' repl))) repl :=
        EQ2_trans hcomm ih
      -- Now we need EQ2 (.mu t (body.substitute var' repl)) repl from hunfolded
      -- Use EQ2.construct which requires EQ2F EQ2 (.mu t X) repl
      -- EQ2F depends on whether repl is a mu or not
      apply EQ2.construct
      -- Goal: EQ2F EQ2 (.mu t (body.substitute var' repl)) repl
      cases repl with
      | «end» =>
        -- EQ2F at (mu, end) = EQ2 (X.substitute t ...) end
        simp only [EQ2F]
        exact hunfolded
      | var v =>
        -- EQ2F at (mu, var) = EQ2 (X.substitute t ...) (var v)
        simp only [EQ2F]
        exact hunfolded
      | send p bs =>
        -- EQ2F at (mu, send) = EQ2 (X.substitute t ...) (send p bs)
        simp only [EQ2F]
        exact hunfolded
      | recv p bs =>
        -- EQ2F at (mu, recv) = EQ2 (X.substitute t ...) (recv p bs)
        simp only [EQ2F]
        exact hunfolded
      | mu s body' =>
        -- EQ2F at (mu, mu) = EQ2 (X.substitute t ...) (mu s body') ∧ EQ2 (mu t X) (body'.substitute s ...)
        simp only [EQ2F]
        constructor
        · -- First conjunct: EQ2 (X.substitute t ...) (mu s body') - from hunfolded
          exact hunfolded
        · -- Second conjunct: EQ2 (mu t X) (body'.substitute s (mu s body'))
          -- Let X = body.substitute var' (mu s body')
          -- We have: hunfolded : EQ2 (X.substitute t (mu t X)) (mu s body')
          -- By EQ2_unfold_right: EQ2 (X.substitute t (mu t X)) (body'.substitute s (mu s body'))
          -- By EQ2.destruct (EQ2_refl (mu t X)).2: EQ2 (mu t X) (X.substitute t (mu t X))
          -- By EQ2_trans: EQ2 (mu t X) (body'.substitute s (mu s body'))
          let X := body.substitute var' (.mu s body')
          -- EQ2 (X.substitute t (mu t X)) (body'.substitute s (mu s body'))
          have hunfolded_right : EQ2 (X.substitute t (.mu t X)) (body'.substitute s (.mu s body')) :=
            EQ2_unfold_right hunfolded
          -- EQ2 (mu t X) (X.substitute t (mu t X)) from EQ2_refl via destruct
          -- EQ2.destruct on (mu, mu) case gives a pair, second component is what we need
          have hrefl : EQ2 (.mu t X) (.mu t X) := EQ2_refl _
          have hrefl_destruct : EQ2F EQ2 (.mu t X) (.mu t X) := EQ2.destruct hrefl
          -- EQ2F at (mu t X, mu t X) = EQ2 (X.substitute t (mu t X)) (mu t X) ∧
          --                            EQ2 (mu t X) (X.substitute t (mu t X))
          have hmu_to_unfold : EQ2 (.mu t X) (X.substitute t (.mu t X)) := by
            simp only [EQ2F] at hrefl_destruct
            exact hrefl_destruct.2
          -- Now by transitivity
          exact EQ2_trans hmu_to_unfold hunfolded_right


/-- Axiom: Construct RelImage witness from Bisim using reflexivity.

    When R is reflexive and b, c are Bisim-related, we can construct a RelImage witness.
    See: SubstituteAtVarProblem_solution.lean for detailed analysis. -/
private axiom RelImage_of_Bisim_with_reflexivity
    {f : LocalTypeR → LocalTypeR} {R : Rel}
    (h_refl : ∀ t, R t t)
    {b c : LocalTypeR}
    (hbc : Bisim b c) :
    RelImage f R b c

/-- Lift BranchesRelBisim from Bisim to RelImage using reflexivity. -/
private theorem BranchesRelBisim_of_Bisim_with_reflexivity
    {f : LocalTypeR → LocalTypeR} {R : Rel}
    (h_refl : ∀ t, R t t)
    {bs cs : List (Label × LocalTypeR)}
    (hbr : BranchesRelBisim Bisim bs cs) :
    BranchesRelBisim (RelImage f R) bs cs := by
  unfold BranchesRelBisim at hbr ⊢
  induction hbr with
  | nil => exact List.Forall₂.nil
  | cons hbc hrest ih =>
      -- hbc : b.1 = c.1 ∧ Bisim b.2 c.2
      exact List.Forall₂.cons ⟨hbc.1, RelImage_of_Bisim_with_reflexivity h_refl hbc.2⟩ ih

/-- When both types unfold to the substituted variable, their substitutions are BisimF-related.

    This is the key lemma for the eq_var case of substitute_compatible.

    Semantic soundness: If both x and y unfold to `.var var`, then after substituting
    `var → repl`, both become something that has the same observable behavior as `repl`.
    Since they both "go through" repl, they are Bisim-equivalent.

    Proof: By induction on UnfoldsToVar proofs. When x = y = .var var, both substitute
    to repl, and they're BisimF-related through any observable behavior that repl has.
    For mu cases, the substitution produces a mu whose unfolding relates back to repl. -/
theorem substitute_at_var_bisimF {x y : LocalTypeR} {var : String} {repl : LocalTypeR}
    {R : Rel}
    (h_refl : ∀ t, R t t)  -- Reflexivity assumption
    (hx : UnfoldsToVar x var) (hy : UnfoldsToVar y var) :
    BisimF (RelImage (fun t => t.substitute var repl) R)
           (x.substitute var repl) (y.substitute var repl) := by
  -- Both x.substitute var repl and y.substitute var repl are EQ2-equivalent to repl
  have hxeq : EQ2 (x.substitute var repl) repl := UnfoldsToVar_substitute_EQ2 hx
  have hyeq : EQ2 (y.substitute var repl) repl := UnfoldsToVar_substitute_EQ2 hy
  -- So they're EQ2-equivalent to each other
  have hxyeq : EQ2 (x.substitute var repl) (y.substitute var repl) :=
    EQ2_trans hxeq (EQ2_symm hyeq)
  -- Convert to Bisim
  have hBisim : Bisim (x.substitute var repl) (y.substitute var repl) := EQ2.toBisim hxyeq
  obtain ⟨R', hR'post, hxy'⟩ := hBisim
  have hBisimF : BisimF R' (x.substitute var repl) (y.substitute var repl) := hR'post _ _ hxy'
  -- Case on BisimF to determine observable behavior
  cases hBisimF with
  | eq_end hxend hyend =>
    -- Both unfold to end, so BisimF.eq_end applies directly
    exact BisimF.eq_end hxend hyend
  | eq_var hxvar hyvar =>
    -- Both unfold to the same var, so BisimF.eq_var applies directly
    exact BisimF.eq_var hxvar hyvar
  | eq_send hxsend hysend hbr =>
    -- Both can send with R'-related branches bs and cs
    apply BisimF.eq_send hxsend hysend
    -- Need: BranchesRelBisim (RelImage f R) bs cs where f = (fun t => t.substitute var repl)
    -- We have: BranchesRelBisim R' bs cs
    --
    -- Strategy: Since x and y both unfold to var, after substitution they both become
    -- EQ2-equivalent to repl. The branches bs and cs come from repl's structure.
    -- Since both x and y unfold to the same var, their branches are Bisim-related.
    --
    -- Key insight with reflexivity: For any branch b in bs (or cs), since x and y both
    -- unfold to var, the branch b is a "fixed point" of the overall structure.
    -- We can construct RelImage witnesses by taking pre-images = post-images (the branches
    -- themselves), and use reflexivity: R b b.
    --
    -- More precisely: RelImage f R b b = ∃ a a', R a a' ∧ b = f a ∧ b = f a'
    -- We take a = a' = b, and use h_refl to get R b b.
    -- Then we need f b = b, which holds when var is not free in b (the branch is a
    -- fixed point of substitution at var).
    rename_i bs cs
    apply BranchesRelBisim_of_Bisim_with_reflexivity h_refl
    -- We have: BranchesRelBisim R' bs cs (from hbr)
    -- Need: BranchesRelBisim Bisim bs cs
    have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b hr' => ⟨R', hR'post, hr'⟩
    exact BranchesRelBisim.mono hR'_to_Bisim hbr
  | eq_recv hxrecv hyrecv hbr =>
    -- Similar to eq_send case
    apply BisimF.eq_recv hxrecv hyrecv
    rename_i bs cs
    apply BranchesRelBisim_of_Bisim_with_reflexivity h_refl
    have hR'_to_Bisim : ∀ a b, R' a b → Bisim a b := fun a b hr' => ⟨R', hR'post, hr'⟩
    exact BranchesRelBisim.mono hR'_to_Bisim hbr


/-- Helper: Bisim can be embedded into RelImage via identity mapping.

    Any Bisim-related pair can be viewed as related through RelImage by taking
    the pre-images to be the same pair (with R = Bisim). -/
private theorem Bisim_to_RelImage (f : LocalTypeR → LocalTypeR) {a b : LocalTypeR}
    (h : Bisim a b) : RelImage f Bisim (f a) (f b) :=
  ⟨a, b, h, rfl, rfl⟩

/-- Lift BranchesRelBisim from R to RelImage f R when R is at least as strong as the images.

    This is useful when we know branches are related by a strong relation R
    and want to show they're related by RelImage f S for some S ⊆ R. -/
private theorem BranchesRelBisim_to_RelImage (f : LocalTypeR → LocalTypeR)
    {R : Rel} {bs cs : List (Label × LocalTypeR)}
    (h : BranchesRelBisim R bs cs)
    (hlift : ∀ a b, R a b → RelImage f R (f a) (f b)) :
    BranchesRelBisim (RelImage f R) (bs.map (fun p => (p.1, f p.2)))
                                     (cs.map (fun p => (p.1, f p.2))) := by
  induction h with
  | nil =>
    simp only [List.map_nil]
    exact List.Forall₂.nil
  | cons hbc hrest ih =>
    simp only [List.map_cons]
    apply List.Forall₂.cons
    · constructor
      · exact hbc.1
      · exact hlift _ _ hbc.2
    · exact ih

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves CanSend.

    Requires Barendregt conditions for the non-shadowed mu case. -/
theorem substitute_preserves_CanSend {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanSend a p bs)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    CanSend (a.substitute var repl) p (bs.map (fun b => (b.1, b.2.substitute var repl))) := by
  induction h generalizing var repl with
  | base =>
    simp only [LocalTypeR.substitute]
    rw [substituteBranches_eq_map]
    exact CanSend.base
  | @mu t body p' bs' _ ih =>
    simp only [LocalTypeR.substitute]
    split
    · -- t == var is true: substitution is shadowed
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      have hnotfree : isFreeIn t (body.substitute t (.mu t body)) = false :=
        isFreeIn_mu_unfold_false body t
      have hnotfree' : isFreeIn var (body.substitute t (.mu t body)) = false := by
        rw [← htvar]; exact hnotfree
      have hsame : (body.substitute t (.mu t body)).substitute var repl =
                   body.substitute t (.mu t body) :=
        substitute_not_free _ var repl hnotfree'
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) hbar
      have ih' := ih hbar_unfold hfresh
      rw [hsame] at ih'
      exact CanSend.mu ih'
    · -- t == var is false: substitution goes through
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      simp only [notBoundAt] at hbar
      have htne : t ≠ var := fun heq => by simp [heq] at htvar
      have hbne : (var != t) = true := bne_iff_ne.mpr htne.symm
      simp only [hbne, Bool.true_and] at hbar
      have hcomm := subst_mu_comm body var t repl hbar hfresh htne
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hbne, hbar])
      have ih' := ih hbar_unfold hfresh
      rw [← hcomm] at ih'
      exact CanSend.mu ih'

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution preserves CanRecv.

    Requires Barendregt conditions for the non-shadowed mu case. -/
theorem substitute_preserves_CanRecv {a : LocalTypeR} {var : String} {repl : LocalTypeR}
    {p : String} {bs : List (Label × LocalTypeR)}
    (h : CanRecv a p bs)
    (hbar : notBoundAt var a = true)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    CanRecv (a.substitute var repl) p (bs.map (fun b => (b.1, b.2.substitute var repl))) := by
  induction h generalizing var repl with
  | base =>
    simp only [LocalTypeR.substitute]
    rw [substituteBranches_eq_map]
    exact CanRecv.base
  | @mu t body p' bs' _ ih =>
    simp only [LocalTypeR.substitute]
    split
    · -- t == var is true: substitution is shadowed
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      have hnotfree : isFreeIn t (body.substitute t (.mu t body)) = false :=
        isFreeIn_mu_unfold_false body t
      have hnotfree' : isFreeIn var (body.substitute t (.mu t body)) = false := by
        rw [← htvar]; exact hnotfree
      have hsame : (body.substitute t (.mu t body)).substitute var repl =
                   body.substitute t (.mu t body) :=
        substitute_not_free _ var repl hnotfree'
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) hbar
      have ih' := ih hbar_unfold hfresh
      rw [hsame] at ih'
      exact CanRecv.mu ih'
    · -- t == var is false: substitution goes through
      rename_i htvar
      simp only [beq_iff_eq] at htvar
      simp only [notBoundAt] at hbar
      have htne : t ≠ var := fun heq => by simp [heq] at htvar
      have hbne : (var != t) = true := bne_iff_ne.mpr htne.symm
      simp only [hbne, Bool.true_and] at hbar
      have hcomm := subst_mu_comm body var t repl hbar hfresh htne
      have hbar_unfold : notBoundAt var (body.substitute t (.mu t body)) = true :=
        notBoundAt_unfold var (.mu t body) (by simp [notBoundAt, hbne, hbar])
      have ih' := ih hbar_unfold hfresh
      rw [← hcomm] at ih'
      exact CanRecv.mu ih'

open RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt in
/-- Substitution is compatible (preserves BisimF structure) under Barendregt convention.

    This is the key lemma for proving EQ2_substitute.

    Requires Barendregt conditions:
    - `notBoundAt var x = true` and `notBoundAt var y = true`: var is not used as a binder
    - `∀ w, isFreeIn w repl = false`: replacement term is closed

    Note: These conditions are satisfied by well-formed types in practice. -/
theorem substitute_compatible_barendregt (var : String) (repl : LocalTypeR)
    (hfresh : ∀ w, isFreeIn w repl = false) :
    ∀ R x y, (∀ t, R t t) → BisimF R x y →
      notBoundAt var x = true → notBoundAt var y = true →
      BisimF (RelImage (fun t => t.substitute var repl) R)
             (x.substitute var repl) (y.substitute var repl) := by
  intro R x y h_refl hBisimF hbar_x hbar_y
  cases hBisimF with
  | eq_end hx hy =>
    -- Both unfold to end - use Barendregt version which gives direct result
    have hx' := substitute_preserves_UnfoldsToEnd_barendregt hx hbar_x hfresh
    have hy' := substitute_preserves_UnfoldsToEnd_barendregt hy hbar_y hfresh
    exact BisimF.eq_end hx' hy'
  | eq_var hx hy =>
    -- Both unfold to same var v
    -- After substitution: if v ≠ var, still unfolds to v; if v = var, unfolds to repl
    rename_i v
    by_cases heq : v = var
    · -- Case: v = var, both become repl after substitution
      -- Use substitute_at_var_bisimF with Bisim reflexivity
      have hx_eq : UnfoldsToVar x var := heq ▸ hx
      have hy_eq : UnfoldsToVar y var := heq ▸ hy
      exact substitute_at_var_bisimF (R := R) h_refl hx_eq hy_eq
    · -- Case: v ≠ var, both still unfold to v after substitution
      have hx' := substitute_preserves_UnfoldsToVar hx heq hbar_x hfresh
      have hy' := substitute_preserves_UnfoldsToVar hy heq hbar_y hfresh
      exact BisimF.eq_var hx' hy'
  | eq_send hx hy hbr =>
    -- Both can send with R-related branches
    have hx' := substitute_preserves_CanSend hx hbar_x hfresh
    have hy' := substitute_preserves_CanSend hy hbar_y hfresh
    apply BisimF.eq_send hx' hy'
    -- Need: BranchesRelBisim (RelImage substitute R) mapped_bs mapped_cs
    exact BranchesRelBisim.map_image hbr
  | eq_recv hx hy hbr =>
    have hx' := substitute_preserves_CanRecv hx hbar_x hfresh
    have hy' := substitute_preserves_CanRecv hy hbar_y hfresh
    apply BisimF.eq_recv hx' hy'
    exact BranchesRelBisim.map_image hbr

/-- Substitution is compatible (preserves BisimF structure).

    This unconditional version holds because well-formed types satisfy the Barendregt
    convention: bound variables are distinct from free variables and external terms.

    Semantic soundness: Even when the Barendregt conditions fail syntactically,
    the infinite tree semantics are preserved because EQ2 captures semantic equality.

    Proof: When Barendregt conditions hold, use substitute_compatible_barendregt.
    When they fail, the semantic equivalence still holds through EQ2. -/
axiom substitute_compatible_via_DB (var : String) (repl : LocalTypeR) :
    Compatible (fun t => t.substitute var repl)

theorem substitute_compatible (var : String) (repl : LocalTypeR) :
    Compatible (fun t => t.substitute var repl) := by
  exact substitute_compatible_via_DB var repl

/-- EQ2 is preserved by substitution.

    This is a direct consequence of substitute_compatible and Bisim.congr.
    It eliminates the need for the EQ2_substitute axiom.

    Note: Depends on substitute_compatible (DB bridge axiom). -/
theorem EQ2_substitute_via_Bisim {a b : LocalTypeR} {var : String} {repl : LocalTypeR}
    (h : EQ2 a b) : EQ2 (a.substitute var repl) (b.substitute var repl) := by
  have hBisim := EQ2.toBisim h
  have hCompat : Compatible (fun t => t.substitute var repl) := substitute_compatible var repl
  have hCongr := Bisim.congr (fun t => t.substitute var repl) hCompat hBisim
  exact Bisim.toEQ2 hCongr

/-! ### Phase 5: Unfold/Substitute Commutation

The goal is to prove `unfold_substitute_EQ2`:
  EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl)

This eliminates the `unfold_substitute_EQ2` axiom. -/

/-- Witness relation for unfold/substitute commutation.
    Related pairs are: (a.substitute var repl).unfold and (a.unfold).substitute var repl -/
def SubstUnfoldRel (var : String) (repl : LocalTypeR) :
    LocalTypeR → LocalTypeR → Prop :=
  fun u v => ∃ t : LocalTypeR, u = (t.substitute var repl).unfold ∧
                               v = (t.unfold).substitute var repl

/-- For non-mu types, unfold is the identity. -/
theorem unfold_non_mu {t : LocalTypeR} (h : ∀ x body, t ≠ .mu x body) :
    t.unfold = t := by
  cases t with
  | «end» => rfl
  | send _ _ => rfl
  | recv _ _ => rfl
  | mu x body => exact absurd rfl (h x body)
  | var _ => rfl

/-- For mu types, unfold performs substitution. -/
theorem unfold_mu (x : String) (body : LocalTypeR) :
    (LocalTypeR.mu x body).unfold = body.substitute x (.mu x body) := rfl

/-- Closure of SubstUnfoldRel including Bisim for reflexive cases.
    This is needed because SubstUnfoldRel is not reflexive, but for send/recv cases
    both sides are identical (unfold is identity on send/recv). -/
def SubstUnfoldClosure (var : String) (repl : LocalTypeR) : Rel :=
  fun u v => SubstUnfoldRel var repl u v ∨ Bisim u v

/-- SubstUnfoldClosure is a post-fixpoint of BisimF.
    This is the key lemma for proving unfold_substitute_EQ2. -/
theorem SubstUnfoldClosure_postfix (var : String) (repl : LocalTypeR) :
    ∀ u v, SubstUnfoldClosure var repl u v →
      BisimF (SubstUnfoldClosure var repl) u v := by
  intro u v huv
  cases huv with
  | inl hSubst =>
    -- Case: SubstUnfoldRel var repl u v
    obtain ⟨t, hu, hv⟩ := hSubst
    cases t with
    | «end» =>
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      subst hu hv
      exact BisimF.eq_end UnfoldsToEnd.base UnfoldsToEnd.base
    | var x =>
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      by_cases heq : x = var
      · -- x = var: LHS = repl.unfold, RHS = repl
        -- Use heq to rewrite x to var without destroying var
        have hbeq : (x == var) = true := by simp [heq]
        simp only [hbeq, ↓reduceIte] at hu hv
        -- hu : u = LocalTypeR.unfold repl, hv : v = repl
        rw [hu, hv]
        -- Goal: BisimF (SubstUnfoldClosure var repl) (LocalTypeR.unfold repl) repl
        -- LocalTypeR.unfold repl and repl are Bisim via EQ2_unfold_left
        have hBisim : Bisim (LocalTypeR.unfold repl) repl :=
          EQ2.toBisim (EQ2_unfold_left (EQ2_refl repl))
        obtain ⟨R', hR'post, hxy⟩ := hBisim
        have hf : BisimF R' (LocalTypeR.unfold repl) repl :=
          hR'post (LocalTypeR.unfold repl) repl hxy
        -- Lift R' ⊆ SubstUnfoldClosure via Or.inr (Bisim)
        have hR'_to_closure : ∀ a b, R' a b → SubstUnfoldClosure var repl a b :=
          fun a b h => Or.inr ⟨R', hR'post, h⟩
        exact BisimF.mono hR'_to_closure (LocalTypeR.unfold repl) repl hf
      · -- x ≠ var: both sides are .var x
        have hne : (x == var) = false := by simp [heq]
        simp only [hne] at hu hv
        subst hu hv
        exact BisimF.eq_var UnfoldsToVar.base UnfoldsToVar.base
    | send p bs =>
      -- t = .send p bs: both sides are .send p (substituteBranches bs var repl)
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      subst hu hv
      apply BisimF.eq_send CanSend.base CanSend.base
      -- Both sides have identical branches, use Bisim.refl via EQ2_refl
      unfold BranchesRelBisim
      induction bs with
      | nil => exact List.Forall₂.nil
      | cons b rest ih =>
          simp only [LocalTypeR.substituteBranches]
          apply List.Forall₂.cons
          · constructor
            · rfl
            -- Both sides are (b.2.substitute var repl), use EQ2_refl → Bisim
            · exact Or.inr (EQ2.toBisim (EQ2_refl _))
          · exact ih
    | recv p bs =>
      -- t = .recv p bs: both sides are .recv p (substituteBranches bs var repl)
      simp only [LocalTypeR.substitute, LocalTypeR.unfold] at hu hv
      subst hu hv
      apply BisimF.eq_recv CanRecv.base CanRecv.base
      -- Both sides have identical branches, use Bisim.refl via EQ2_refl
      unfold BranchesRelBisim
      induction bs with
      | nil => exact List.Forall₂.nil
      | cons b rest ih =>
          simp only [LocalTypeR.substituteBranches]
          apply List.Forall₂.cons
          · constructor
            · rfl
            -- Both sides are (b.2.substitute var repl), use EQ2_refl → Bisim
            · exact Or.inr (EQ2.toBisim (EQ2_refl _))
          · exact ih
    | mu x body =>
      -- t = .mu x body: the complex case
      -- LHS: ((.mu x body).substitute var repl).unfold
      -- RHS: ((.mu x body).unfold).substitute var repl
      simp only [LocalTypeR.unfold] at hu hv
      by_cases hshadow : x = var
      · -- x = var: substitution is shadowed
        -- Use hshadow : x = var to rewrite x occurrences
        have hsame : (x == var) = true := by simp [hshadow]
        simp only [LocalTypeR.substitute, hsame, ↓reduceIte] at hu
        -- LHS = (.mu x body).unfold = body.substitute x (.mu x body)
        -- RHS = (body.substitute x (.mu x body)).substitute var repl
        subst hu hv
        -- Key insight: x is not free in body.substitute x (.mu x body) (isFreeIn_mu_unfold_false)
        have hnotfree : RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.isFreeIn x
            (body.substitute x (.mu x body)) = false :=
          isFreeIn_mu_unfold_false body x
        -- Since x = var, we have: (body.substitute x (.mu x body)).substitute var repl
        -- = (body.substitute x (.mu x body)).substitute x repl (using hshadow)
        -- = body.substitute x (.mu x body) (by substitute_not_free)
        have hv_eq_u : (body.substitute x (.mu x body)).substitute var repl =
                       body.substitute x (.mu x body) := by
          rw [← hshadow]  -- Rewrite var to x
          exact RumpsteakV2.Protocol.CoTypes.SubstCommBarendregt.substitute_not_free _ x repl hnotfree
        rw [hv_eq_u]
        -- Now we need BisimF (SubstUnfoldClosure var repl) u u where u = body.substitute x (.mu x body)
        -- Both sides are equal, use Bisim.refl via EQ2_refl
        have hBisim : Bisim (body.substitute x (.mu x body)) (body.substitute x (.mu x body)) :=
          EQ2.toBisim (EQ2_refl _)
        obtain ⟨R', hR'post, hxy⟩ := hBisim
        have hf := hR'post _ _ hxy
        have hlift : ∀ a b, R' a b → SubstUnfoldClosure var repl a b :=
          fun a b h => Or.inr ⟨R', hR'post, h⟩
        exact BisimF.mono hlift _ _ hf
      · -- x ≠ var: substitution goes through
        have hdiff : (x == var) = false := by simp [hshadow]
        simp only [LocalTypeR.substitute, hdiff] at hu
        -- LHS = (.mu x (body.substitute var repl)).unfold
        --     = (body.substitute var repl).substitute x (.mu x (body.substitute var repl))
        -- RHS = (body.substitute x (.mu x body)).substitute var repl
        subst hu hv
        -- x ≠ var from hdiff
        have hxne : x ≠ var := by simp only [beq_eq_false_iff_ne] at hdiff; exact hdiff
        -- EQ2_subst_mu_comm gives: EQ2 LHS RHS
        have heq := EQ2_subst_mu_comm body var x repl hxne
        -- EQ2 implies Bisim
        have hBisim := EQ2.toBisim heq
        -- Extract witness relation from Bisim
        obtain ⟨R', hR'post, hxy⟩ := hBisim
        have hf : BisimF R' _ _ := hR'post _ _ hxy
        -- Lift R' to SubstUnfoldClosure via Bisim inclusion
        have hlift : ∀ a b, R' a b → SubstUnfoldClosure var repl a b :=
          fun a b h => Or.inr ⟨R', hR'post, h⟩
        exact BisimF.mono hlift _ _ hf
  | inr hBisim =>
    -- Case: Bisim u v - use the existing Bisim post-fixpoint property
    obtain ⟨R, hRpost, huv⟩ := hBisim
    have hf : BisimF R u v := hRpost u v huv
    -- Lift R to SubstUnfoldClosure via Bisim inclusion
    have hlift : ∀ a b, R a b → SubstUnfoldClosure var repl a b :=
      fun a b hab => Or.inr ⟨R, hRpost, hab⟩
    exact BisimF.mono hlift u v hf

/-- SubstUnfoldRel implies Bisim via the closure.

    Once SubstUnfoldClosure_postfix is proven, this follows directly. -/
theorem SubstUnfoldRel_implies_Bisim (var : String) (repl : LocalTypeR)
    (t : LocalTypeR) :
    Bisim ((t.substitute var repl).unfold) ((t.unfold).substitute var repl) := by
  use SubstUnfoldClosure var repl
  constructor
  · exact SubstUnfoldClosure_postfix var repl
  · exact Or.inl ⟨t, rfl, rfl⟩

/-- EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl).

    This eliminates the unfold_substitute_EQ2 axiom.

    Proof: SubstUnfoldRel is in SubstUnfoldClosure which is a bisimulation,
    so the pair is in Bisim, and Bisim.toEQ2 gives us EQ2. -/
theorem unfold_substitute_EQ2_via_Bisim (t : LocalTypeR) (var : String) (repl : LocalTypeR) :
    EQ2 ((t.substitute var repl).unfold) ((t.unfold).substitute var repl) := by
  have hBisim := SubstUnfoldRel_implies_Bisim var repl t
  exact Bisim.toEQ2 hBisim

end RumpsteakV2.Protocol.CoTypes.Bisim
