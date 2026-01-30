import Telltale.Protocol.LocalTypeR
import Telltale.Protocol.CoTypes.EQ2
import Telltale.Protocol.CoTypes.CoinductiveRel
import Telltale.Protocol.CoTypes.DBBridge
import Telltale.Protocol.CoTypes.Observable
import Telltale.Protocol.CoTypes.Dual
import Telltale.Protocol.CoTypes.SubstCommBarendregt

set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false

/-! # Telltale.Protocol.CoTypes.Bisim

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

namespace Telltale.Protocol.CoTypes.Bisim

open Telltale.Protocol.GlobalType
open Telltale.Protocol.LocalTypeR
open Telltale.Protocol.CoTypes.EQ2
open Telltale.Protocol.CoTypes.Observable
open Telltale.Protocol.CoTypes.CoinductiveRel

/-! ## Observable Behavior

The membership predicates (UnfoldsToEnd, UnfoldsToVar, CanSend, CanRecv) and their
basic properties are defined in Observable.lean to avoid circular dependencies. -/

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

/-- Well-formed local types have observable behavior. -/
theorem LocalTypeR.WellFormed.observable {t : LocalTypeR} (h : LocalTypeR.WellFormed t) :
    Observable t :=
  observable_of_closed_contractive h.closed h.contractive

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

/-! ### Send/Recv Duality for Bounded Paths

These lemmas establish the duality between `CanSendPathBounded` and `CanRecvPathBounded`,
allowing recv lemmas to be derived from send lemmas. -/

/-- CanSendPathBounded on dual type gives CanRecvPathBounded. -/
theorem CanSendPathBounded.to_CanRecvPathBounded_dual {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanSendPathBounded n p bs a) :
    CanRecvPathBounded n p (dualBranches bs) a.dual := by
  induction h with
  | base => exact CanRecvPathBounded.base
  | @step n p bs t body _ ih =>
      simp only [LocalTypeR.dual]
      have heq : (body.substitute t (.mu t body)).dual =
          body.dual.substitute t (.mu t body.dual) := LocalTypeR.dual_substitute body t (.mu t body)
      rw [heq] at ih
      exact CanRecvPathBounded.step ih

/-- CanRecvPathBounded on dual type gives CanSendPathBounded. -/
theorem CanRecvPathBounded.to_CanSendPathBounded_dual {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanRecvPathBounded n p bs a) :
    CanSendPathBounded n p (dualBranches bs) a.dual := by
  induction h with
  | base => exact CanSendPathBounded.base
  | @step n p bs t body _ ih =>
      simp only [LocalTypeR.dual]
      have heq : (body.substitute t (.mu t body)).dual =
          body.dual.substitute t (.mu t body.dual) := LocalTypeR.dual_substitute body t (.mu t body)
      rw [heq] at ih
      exact CanSendPathBounded.step ih

/-- CanRecvPathBounded is equivalent to CanSendPathBounded on dual type with dual branches. -/
theorem CanRecvPathBounded_iff_CanSendPathBounded_dual {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR} :
    CanRecvPathBounded n p bs a ↔ CanSendPathBounded n p (dualBranches bs) a.dual := by
  constructor
  · exact CanRecvPathBounded.to_CanSendPathBounded_dual
  · intro h
    have h' := CanSendPathBounded.to_CanRecvPathBounded_dual h
    simp only [dualBranches_dualBranches, LocalTypeR.dual_dual] at h'
    exact h'

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
  refine UnfoldsToEnd.rec (motive := fun a _ => ∃ n, UnfoldPathEndBounded n a) ?base ?mu h
  · exact ⟨0, UnfoldPathEndBounded.base⟩
  · intro t body h' ih
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
  refine UnfoldsToVar.rec (motive := fun a v _ => ∃ n, UnfoldPathVarBounded n v a) ?base ?mu h
  · exact ⟨0, UnfoldPathVarBounded.base⟩
  · intro t body v' h' ih
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
  refine CanSend.rec (motive := fun a p bs _ => ∃ n, CanSendPathBounded n p bs a) ?base ?mu h
  · exact ⟨0, CanSendPathBounded.base⟩
  · intro t body p' bs' h' ih
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, CanSendPathBounded.step hn⟩

/-- Bounded recv path implies unbounded.
    Derived from `CanSendPathBounded.toCanSend` via duality. -/
theorem CanRecvPathBounded.toCanRecv {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanRecvPathBounded n p bs a) : CanRecv a p bs := by
  -- Dualize to send, then dualize back.
  simpa [dualBranches_dualBranches, LocalTypeR.dual_dual] using
    (CanSend.dual
      (CanSendPathBounded.toCanSend (CanRecvPathBounded.to_CanSendPathBounded_dual h)))

/-- Unbounded recv implies bounded.
    Derived from `CanSend.toBounded` via duality. -/
theorem CanRecv.toBounded {p : String} {bs : List (Label × LocalTypeR)} {a : LocalTypeR}
    (h : CanRecv a p bs) : ∃ n, CanRecvPathBounded n p bs a := by
  -- Dualize to send, bound, then dualize back.
  have hsend : CanSend a.dual p (dualBranches bs) := CanRecv.dual h
  obtain ⟨n, hn⟩ := CanSend.toBounded hsend
  refine ⟨n, ?_⟩
  simpa [dualBranches_dualBranches, LocalTypeR.dual_dual] using
    (CanSendPathBounded.to_CanRecvPathBounded_dual hn)


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
theorem CanSendPathBounded.unfold_iter_eq {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR} :
    CanSendPathBounded n p bs a → (LocalTypeR.unfold^[n] a = .send p bs) := by
  intro h
  induction h with
  | base => simp [Function.iterate_zero, id_eq]
  | step h ih =>
      simpa [LocalTypeR.unfold, Function.iterate_succ_apply] using ih

/-- Bounded recv path yields a concrete unfold iteration.
    Derived from `CanSendPathBounded.unfold_iter_eq` via duality. -/
theorem CanRecvPathBounded.unfold_iter_eq {n : ℕ} {p : String}
    {bs : List (Label × LocalTypeR)} {a : LocalTypeR} :
    CanRecvPathBounded n p bs a → (LocalTypeR.unfold^[n] a = .recv p bs) := by
  intro h
  -- Convert to send on the dual, then dualize the unfold equality.
  have heq : (LocalTypeR.unfold^[n] a).dual = .send p (dualBranches bs) := by
    have hsend := CanRecvPathBounded.to_CanSendPathBounded_dual h
    simpa [unfold_iter_dual n a] using (CanSendPathBounded.unfold_iter_eq hsend)
  have hinv := congrArg LocalTypeR.dual heq
  simpa [LocalTypeR.dual_dual, LocalTypeR.dual, dualBranches_dualBranches] using hinv
end Telltale.Protocol.CoTypes.Bisim
