import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Iterate
import RumpsteakV2.Protocol.GlobalType

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

theorem freeVarsOfBranches_eq_flatMap (branches : List (Label × LocalTypeR)) :
    freeVarsOfBranches branches = branches.flatMap (fun (_, t) => t.freeVars) := by
  induction branches with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | mk label t =>
          simp [freeVarsOfBranches, ih, List.flatMap]

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
theorem substituteBranches_eq_map (bs : List (Label × LocalTypeR)) (var : String) (repl : LocalTypeR) :
    substituteBranches bs var repl = bs.map (fun (l, c) => (l, c.substitute var repl)) := by
  induction bs with
  | nil => rfl
  | cons head tail ih =>
      simp only [substituteBranches, List.map_cons, ih]

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

/-- A local type is closed if it has no free type variables. -/
def LocalTypeR.isClosed (lt : LocalTypeR) : Bool := lt.freeVars.isEmpty

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

/-! ## Guardedness and muHeight Properties -/

/-- For non-mu types, unfold is identity. -/
theorem LocalTypeR.unfold_non_mu (lt : LocalTypeR) :
    (∀ t body, lt ≠ .mu t body) → lt.unfold = lt := by
  intro h
  match lt with
  | .end | .var _ | .send _ _ | .recv _ _ => rfl
  | .mu t body => exact absurd rfl (h t body)

/-- The result of unfold on a mu is the substituted body. -/
theorem LocalTypeR.unfold_mu (t : String) (body : LocalTypeR) :
    (.mu t body : LocalTypeR).unfold = body.substitute t (.mu t body) := rfl

/-- fullUnfold of mu unfolds via one step of unfold then iterate.

    This follows from the definition: fullUnfold (.mu t body) = unfold^[1 + body.muHeight] (.mu t body)
    and Function.iterate_succ': f^[n+1] x = f^[n] (f x).

    TODO: Complete proof - currently blocked on Function.iterate unfolding. -/
theorem LocalTypeR.fullUnfold_mu (t : String) (body : LocalTypeR) :
    (.mu t body : LocalTypeR).fullUnfold =
      LocalTypeR.unfold^[body.muHeight] (body.substitute t (.mu t body)) := by
  sorry

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

/-! ## Unguarded Variable Theorem (Coq's `eguarded_test`)

This is the key bridge between guardedness and observable behavior.
If a variable is free in a type but NOT guarded, then the type fully
unfolds to that variable.

The intuition is:
- An unguarded free variable sits at the "head" position
- Unfolding only substitutes under mu, so the variable stays at head
- After enough unfolding, we reach just the variable -/

/-- If a variable is not guarded in a type (appears at head position after unfolding),
    then fully unfolding produces that variable.

    This corresponds to Coq's `eguarded_test`:
    ```coq
    Lemma eguarded_test : forall e sigma i, ~~ eguarded i e ->
      iter (emu_height e) eunf e [e sigma] = sigma i.
    ```

    Proof: By well-founded induction on muHeight.
    - Base case (muHeight = 0): The type is either:
      - .var v: If not guarded for v, then v is free and we're done
      - .end/.send/.recv: Variable is trivially guarded (contradiction)
    - Inductive case (.mu t body): If v is not guarded in .mu t body,
      then v ≠ t (otherwise shadowed = guarded) and v is not guarded in body.
      After unfolding: body.substitute t (.mu t body). The variable v is still
      not guarded (unguardedness preserved through substitution when v ≠ t).
      By IH on muHeight(body) < muHeight(.mu t body), we get the result. -/
theorem LocalTypeR.unguarded_unfolds_to_var (lt : LocalTypeR) (v : String)
    (h_free : lt.isFreeIn v = true) (h_not_guarded : lt.isGuarded v = false) :
    lt.fullUnfold = .var v := by
  match lt with
  | .end =>
    -- .end: v is not free in .end (contradiction)
    simp only [isFreeIn] at h_free
    exact absurd h_free (by decide)
  | .var w =>
    -- .var w: If v is free (w = v) and not guarded (w = v), then fullUnfold = .var w = .var v
    simp only [isFreeIn, beq_iff_eq] at h_free
    simp only [h_free, fullUnfold, muHeight, Function.iterate_zero, id_eq]
  | .send _ _ =>
    -- .send: variable is guarded in send (contradiction)
    simp only [isGuarded] at h_not_guarded
    exact absurd h_not_guarded (by decide)
  | .recv _ _ =>
    -- .recv: variable is guarded in recv (contradiction)
    simp only [isGuarded] at h_not_guarded
    exact absurd h_not_guarded (by decide)
  | .mu t body =>
    -- .mu t body: unguarded means v ≠ t and unguarded in body
    simp only [isGuarded] at h_not_guarded
    split at h_not_guarded
    · -- v == t: Then isGuarded = true (contradiction)
      contradiction
    · -- v != t: Then isGuarded = body.isGuarded v = false
      rename_i hvt_false
      simp only [isFreeIn, hvt_false, ↓reduceIte] at h_free
      -- h_free : body.isFreeIn v = true
      -- h_not_guarded : body.isGuarded v = false
      -- We need to show (.mu t body).fullUnfold = .var v
      -- This requires well-founded recursion on muHeight, which is complex
      -- For now, we leave this as sorry and note the proof strategy
      sorry

/-- The converse: if a free variable IS guarded, fullUnfold reaches a non-variable form.

    This is the key property for proving observable_of_closed: closed types
    (with all bound variables guarded) unfold to send/recv/end. -/
theorem LocalTypeR.guarded_fullUnfold_not_var (lt : LocalTypeR) (v : String)
    (h_guarded : lt.isGuarded v = true) :
    ∀ w, lt.fullUnfold ≠ .var w ∨ lt.isFreeIn v = false := by
  intro w
  -- Either v is not free (trivial), or v is guarded (need to show fullUnfold ≠ var)
  by_cases h_free : lt.isFreeIn v = true
  · -- v is free and guarded: fullUnfold reaches non-var
    left
    -- This would follow from unguarded_unfolds_to_var by contraposition
    -- If fullUnfold = .var w, then w must be unguarded, but we assumed guarded
    sorry
  · -- v is not free: trivial
    right
    simp only [Bool.not_eq_true] at h_free
    exact h_free

end RumpsteakV2.Protocol.LocalTypeR
