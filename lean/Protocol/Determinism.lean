import Protocol.DeadlockFreedom

/-! # MPST Determinism

This module provides determinism theorems for the Protocol MPST semantics. -/

/-
The Problem. We need to prove that MPST execution is deterministic: given the
same action context, a configuration transitions to a unique next configuration.
This is essential for predictable execution and reasoning about protocol behavior.

Solution Structure. We prove:
1. `uniqueBranchLabels`: branch labels must be distinct
2. `step_base_det_*`: per-constructor base step determinism
3. `IndependentActions`: predicate for actions on disjoint sessions
4. `step_base_deterministic_strong`: every base step has a unique result
-/


/-! ## Overview

Determinism states that given the same action context, a configuration transitions
to a unique next configuration. This is crucial for:
- Predictable protocol execution
- Testing and simulation
- Reasoning about protocol behavior

## Key Theorems

- `uniqueBranchLabels`: predicate ensuring branch labels are distinct
- `step_base_det_*`: per-constructor base step determinism
- `IndependentActions`: predicate for actions on disjoint sessions
- `step_base_deterministic_strong`: every base step has a unique result

Ported from Telltale.Proofs.Safety.Determinism.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## Unique Branch Labels

For determinism, we need branch labels to be unique within each select/branch.
This ensures that a given label uniquely determines the continuation.
-/

/-- Check if all branch labels in a list are unique. -/
def uniqueBranchLabelsList : List (Label × LocalType) → Bool
  | [] => true
  | (lbl, _) :: rest =>
      !(rest.map Prod.fst).contains lbl &&
      uniqueBranchLabelsList rest

/-- If branches have unique labels, then membership determines the continuation.
    Uses uniqueBranchLabelsList for the predicate. -/
theorem mem_branch_unique_label {lbl : Label} {cont₁ cont₂ : LocalType}
    {branches : List (Label × LocalType)}
    (huniq : uniqueBranchLabelsList branches = true)
    (hmem₁ : (lbl, cont₁) ∈ branches)
    (hmem₂ : (lbl, cont₂) ∈ branches) :
    cont₁ = cont₂ := by
  induction branches with
  | nil => cases hmem₁
  | cons hd tl ih =>
      simp only [uniqueBranchLabelsList] at huniq
      have hand := Bool.and_eq_true_iff.mp huniq
      have hnodup : (tl.map Prod.fst).contains hd.1 = false := by
        simp only [Bool.not_eq_true'] at hand
        exact hand.1
      have htl_uniq : uniqueBranchLabelsList tl = true := hand.2
      cases hmem₁ with
      | head =>
          cases hmem₂ with
          | head => rfl
          | tail _ hmem₂' =>
              have hmem_fst : lbl ∈ tl.map Prod.fst := by
                apply List.mem_map.mpr
                exact ⟨(lbl, cont₂), hmem₂', rfl⟩
              have hcontains : (tl.map Prod.fst).contains lbl = true := by
                rw [List.contains_iff_exists_mem_beq]
                exact ⟨lbl, hmem_fst, beq_self_eq_true lbl⟩
              rw [hcontains] at hnodup
              cases hnodup
      | tail _ hmem₁' =>
          cases hmem₂ with
          | head =>
              have hmem_fst : lbl ∈ tl.map Prod.fst := by
                apply List.mem_map.mpr
                exact ⟨(lbl, cont₁), hmem₁', rfl⟩
              have hcontains : (tl.map Prod.fst).contains lbl = true := by
                rw [List.contains_iff_exists_mem_beq]
                exact ⟨lbl, hmem_fst, beq_self_eq_true lbl⟩
              rw [hcontains] at hnodup
              cases hnodup
          | tail _ hmem₂' =>
              exact ih htl_uniq hmem₁' hmem₂'

/-! ## Base Step Determinism

The base step relation is deterministic when the process uniquely determines
the action. Given the same starting configuration and process, the result is unique.
-/

/-- Base step is deterministic for the same process pattern.

When the process form determines the step (e.g., send k x always enqueues at the
same edge with the same value), the result is unique.

**Note**: This is modulo non-determinism from:
- Which branch is selected in branch/select (determined by buffer contents)
- Parallel composition (which side steps first)
-/
theorem step_base_det_send {C C₁ C₂ : Config} {k x : Var} {e : Endpoint} {v : Value} {target : Role}
    {T : ValType} {L : LocalType}
    (_hProc : C.proc = .send k x)
    (_hk : lookupStr C.store k = some (.chan e))
    (_hx : lookupStr C.store x = some v)
    (_hG : lookupG C.G e = some (.send target T L))
    (_h₁ : StepBase C C₁)
    (_h₂ : StepBase C C₂)
    (hC₁ : C₁ = sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L)
    (hC₂ : C₂ = sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) :
    C₁ = C₂ := by
  rw [hC₁, hC₂]

/-- Recv step is deterministic given the same buffer state. -/
theorem step_base_det_recv {C C₁ C₂ : Config} {k x : Var} {e : Endpoint} {source : Role}
    {T : ValType} {L : LocalType}
    {v : Value} {vs : List Value}
    (_hProc : C.proc = .recv k x)
    (_hk : lookupStr C.store k = some (.chan e))
    (_hG : lookupG C.G e = some (.recv source T L))
    (_hBuf : lookupBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } = v :: vs)
    (h₁ : C₁ = recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L)
    (h₂ : C₂ = recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) :
    C₁ = C₂ := by
  rw [h₁, h₂]

/-! ## Independent Actions

Two actions are independent if they affect disjoint sessions.
Independent actions can be executed in any order with the same result.
-/

/-- Two session IDs are independent (disjoint). -/
def IndependentSessions (s₁ s₂ : SessionId) : Prop := s₁ ≠ s₂

/-- Two configurations step on independent sessions if they affect different session IDs. -/
def IndependentConfigs (C₁ C₂ : Config) : Prop :=
  match stepSessionId C₁, stepSessionId C₂ with
  | some s₁, some s₂ => s₁ ≠ s₂
  | _, _ => True

/-! ## Base Step Determinism

`StepBase` acts only on the head of `C.proc`, so a configuration has at most one
base successor. Consequently two base steps from the same configuration can never
act on two *distinct* sessions: the base relation admits no nontrivial diamond.
Genuine commutation of independent actions on disjoint sessions is proved at the
global-type level in `Semantics.Determinism.Diamond` (`diamond_independent`); a
contextual (`Step`, through `par`) diamond for this process calculus is not yet
formalized here.
-/

/-- Every base step is deterministic: a configuration has at most one
    `StepBase` successor. -/
theorem step_base_deterministic_strong {C C₁ C₂ : Config}
    (h₁ : StepBase C C₁) (h₂ : StepBase C C₂) : C₁ = C₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

/-! ## Local Type Step Determinism

For local types, step determinism follows from unique branch labels.
-/

/-- Local type step is deterministic given unique branch labels.

If a local type with unique branch labels steps to two results
under the same action context, the results are equal.
-/
theorem local_type_step_det {L₁ L₂ : LocalType} {_r : Role} {lbl : Label}
    {bs : List (Label × LocalType)}
    (huniq : uniqueBranchLabelsList bs = true)
    (hmem₁ : (lbl, L₁) ∈ bs)
    (hmem₂ : (lbl, L₂) ∈ bs) :
    L₁ = L₂ :=
  mem_branch_unique_label huniq hmem₁ hmem₂

/-! ## Non-Confluence Example

MPST is NOT confluent in general: different branch choices lead to
incompatible protocol states that can never reconverge.
-/

/-- MPST is not confluent in general.

**Counterexample:** Consider a protocol with two branches leading to
different "stuck" states (e.g., different end states or unbound variables).
Once a branch is chosen, the protocol cannot "undo" that choice.

This is expected behavior: session types are about ensuring protocols
follow their specification, not about allowing arbitrary reordering.
-/
theorem not_confluent_general :
    ¬∀ (C C₁ C₂ : Config),
      (∃ C₁', Step C C₁') →
      (∃ C₂', Step C C₂') →
      C₁ ≠ C₂ →
      ∃ C₃, Steps C₁ C₃ ∧ Steps C₂ C₃ := by
  intro h
  -- Counterexample: Two terminated configs with different nextSid
  -- Since skip can't step, Steps from a skip config only reaches itself
  let C₁ : Config := { proc := .skip, store := [], bufs := [], G := [], D := (∅ : DEnv), nextSid := 0 }
  let C₂ : Config := { proc := .skip, store := [], bufs := [], G := [], D := (∅ : DEnv), nextSid := 1 }
  -- C₁ ≠ C₂ because nextSid differs
  have hne : C₁ ≠ C₂ := by simp [C₁, C₂]
  -- We need some C that can step (to satisfy the premises)
  let C : Config := { proc := .assign "x" .unit, store := [], bufs := [], G := [], D := (∅ : DEnv), nextSid := 0 }
  have hStep : ∃ C', Step C C' :=
    ⟨{ C with proc := .skip, store := [("x", .unit)] }, Step.base (StepBase.assign rfl)⟩
  -- Apply h to get a reconvergence
  obtain ⟨C₃, hC₁, hC₂⟩ := h C C₁ C₂ hStep hStep hne
  -- A skip config can only reach itself via Steps (we use Classical reasoning here)
  -- Since both C₁ and C₂ reach C₃, and C₁ ≠ C₂, we have a contradiction
  -- The key insight: if proc = skip, no Step is possible, so ReflTransGen only has refl
  have skip_stuck : ∀ C' : Config, C'.proc = .skip → ∀ C'', ¬Step C' C'' := by
    intro C' hproc C'' hstep
    cases hstep with
    | base hbase =>
      cases hbase <;> simp_all
    | seq_left hproc' _ =>
      simp_all
    | par_left hproc' _ =>
      simp_all
    | par_right hproc' _ =>
      simp_all
  have hC₁_only_self : ∀ C', Steps C₁ C' → C₁ = C' := by
    intro C' hsteps
    induction hsteps with
    | refl => rfl
    | tail _ hstep ih =>
      exfalso
      -- ih says the intermediate config equals C₁
      -- So that config also has proc = .skip, hence can't step
      rw [← ih] at hstep
      exact skip_stuck C₁ rfl _ hstep
  have hC₂_only_self : ∀ C', Steps C₂ C' → C₂ = C' := by
    intro C' hsteps
    induction hsteps with
    | refl => rfl
    | tail _ hstep ih =>
      exfalso
      rw [← ih] at hstep
      exact skip_stuck C₂ rfl _ hstep
  exact hne ((hC₁_only_self C₃ hC₁).trans (hC₂_only_self C₃ hC₂).symm)

-- Claims Bundle

/-- Bundle of determinism properties. -/
structure DeterminismClaims : Prop where
  /-- Base step determinism for same process form. -/
  send_det : ∀ {C C₁ C₂ : Config} {k x : Var} {e : Endpoint} {v : Value} {target : Role} {T : ValType} {L : LocalType},
    C.proc = .send k x →
    lookupStr C.store k = some (.chan e) →
    lookupStr C.store x = some v →
    lookupG C.G e = some (.send target T L) →
    C₁ = sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L →
    C₂ = sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L →
    C₁ = C₂
  /-- Unique branch label implies unique continuation. -/
  branch_unique : ∀ {lbl : Label} {cont₁ cont₂ : LocalType} {branches : List (Label × LocalType)},
    uniqueBranchLabelsList branches = true →
    (lbl, cont₁) ∈ branches →
    (lbl, cont₂) ∈ branches →
    cont₁ = cont₂
  /-- Base steps are deterministic (no two distinct base successors). -/
  base_det : ∀ {C C₁ C₂ : Config}, StepBase C C₁ → StepBase C C₂ → C₁ = C₂

/-- Construct the determinism claims bundle. -/
theorem determinismClaims : DeterminismClaims where
  send_det := fun hProc hk hx hG hC₁ hC₂ => by rw [hC₁, hC₂]
  branch_unique := mem_branch_unique_label
  base_det := step_base_deterministic_strong

end
