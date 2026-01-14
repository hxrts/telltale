import Effects.Semantics

/-!
# MPST Deadlock Freedom

This module provides deadlock freedom infrastructure for MPST.

## Key Definitions

- `ReachesComm`: Predicate indicating a local type can reach a communication action
- `reachesCommDecide`: Decidable checker for ReachesComm (with fuel for recursion)
- `Done`: Configuration has terminated (all processes skip, all types end)
- `CanProgress`: Configuration can take a step
- `Stuck`: Configuration is neither done nor can progress

## Fairness

Deadlock freedom requires a fairness assumption: messages in buffers are
eventually delivered. Without fairness, a receiver could wait forever for
a message that was sent but never delivered.

## Session Isolation

Different sessions don't interfere with each other. A step affecting session
s₁ doesn't change the state of session s₂.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## Guarded Predicate -/

/-- A local type is guarded at depth n if all recursive variable references
    at indices < n appear under communication prefixes.

This ensures that unfolding a μ-type always makes progress toward a
communication action. A guarded type cannot have unproductive recursion
like `μX.X`.

The depth parameter n tracks how many μ-binders we're inside:
- `var m` is valid only if `m < n` (bound by enclosing μ)
- `mu L` increments the depth for checking L -/
inductive Guarded : Nat → LocalType → Prop where
  | send {n r T L} : Guarded n L → Guarded n (.send r T L)
  | recv {n r T L} : Guarded n L → Guarded n (.recv r T L)
  | select {n r bs} : (∀ b, b ∈ bs → Guarded n b.2) → Guarded n (.select r bs)
  | branch {n r bs} : (∀ b, b ∈ bs → Guarded n b.2) → Guarded n (.branch r bs)
  | end_ {n} : Guarded n .end_
  | var {n m} : m < n → Guarded n (.var m)
  | mu {n L} : Guarded (n + 1) L → Guarded n (.mu L)

/-- Decidable checker for guardedness with explicit list recursion. -/
def guardedDecide (n : Nat) (L : LocalType) : Bool :=
  match L with
  | .send _ _ L => guardedDecide n L
  | .recv _ _ L => guardedDecide n L
  | .select _ bs => guardedDecideBranches n bs
  | .branch _ bs => guardedDecideBranches n bs
  | .end_ => true
  | .var m => decide (m < n)
  | .mu L => guardedDecide (n + 1) L
where
  /-- Helper for checking all branches. -/
  guardedDecideBranches (n : Nat) : List (Label × LocalType) → Bool
    | [] => true
    | (_, L) :: rest => guardedDecide n L && guardedDecideBranches n rest

/-- A closed type is guarded if all variables are bound and guarded. -/
def isGuarded (L : LocalType) : Bool := guardedDecide 0 L

/-! ## ReachesComm Predicate -/

/-- A local type can reach a communication action.

This predicate indicates that a type is "progressive" - it will eventually
perform a send, receive, select, or branch action. Types that are stuck
(e.g., unbound variables) or terminated (`end_`) do not reach communication.

Note: For select/branch, we require non-empty branch lists. An empty branch
list would mean no possible continuation, which is effectively stuck. -/
inductive ReachesComm : LocalType → Prop where
  | send {r T L} : ReachesComm (.send r T L)
  | recv {r T L} : ReachesComm (.recv r T L)
  | select {r bs} : bs ≠ [] → ReachesComm (.select r bs)
  | branch {r bs} : bs ≠ [] → ReachesComm (.branch r bs)
  | mu {L} : ReachesComm L.unfold → ReachesComm (.mu L)

/-- Decidable checker for ReachesComm.

For guarded types, we can check without fuel because:
1. Communication prefixes immediately return true
2. μ-unfolding substitutes .var 0 with .mu L, but guardedness ensures
   variable occurrences are under communication prefixes
3. The recursive call is on a structurally smaller term (the body)

Note: This returns false for unguarded types like `μX.X` since .var is stuck. -/
def reachesCommDecide : LocalType → Bool
  | .send _ _ _ => true
  | .recv _ _ _ => true
  | .select _ bs => !bs.isEmpty
  | .branch _ bs => !bs.isEmpty
  | .end_ => false
  | .var _ => false  -- Unbound or unguarded variable = stuck
  | .mu L => reachesCommDecide L  -- Check body directly (guarded types have comm prefix)

/-- ReachesComm is preserved under unfolding. -/
theorem reachesComm_unfold {L : LocalType} (h : ReachesComm (.mu L)) :
    ReachesComm L.unfold := by
  cases h with
  | mu h => exact h

/-- Helper: reachesCommDecide is monotonic under unfolding for guarded types.

For a guarded μ-type, if the body has a communication prefix, unfolding preserves it.
This is because unfold only substitutes variables, and in a guarded type variables
only appear under communication prefixes. -/
theorem reachesComm_body_implies_unfold (L : LocalType)
    (hBody : reachesCommDecide L = true) :
    ReachesComm L.unfold := by
  sorry  -- Proof requires careful analysis of unfold's effect on guarded types

/-- Soundness: if decidable checker returns true, the type reaches communication.

For μ-types, we check the body directly rather than unfolding. This works because:
- If the body has a communication prefix at the top level → ReachesComm
- If the body is μ (nested), recurse
- Variables return false (handled by guardedness assumption externally) -/
theorem reachesCommDecide_sound (L : LocalType) (h : reachesCommDecide L = true) :
    ReachesComm L := by
  cases L with
  | send => exact ReachesComm.send
  | recv => exact ReachesComm.recv
  | select r bs =>
    simp only [reachesCommDecide, Bool.not_eq_true'] at h
    exact ReachesComm.select (fun hemp => by simp [hemp] at h)
  | branch r bs =>
    simp only [reachesCommDecide, Bool.not_eq_true'] at h
    exact ReachesComm.branch (fun hemp => by simp [hemp] at h)
  | end_ => simp [reachesCommDecide] at h
  | var => simp [reachesCommDecide] at h
  | mu body =>
    simp only [reachesCommDecide] at h
    -- For μ-types, we check the body and must show the unfolded body reaches comm
    exact ReachesComm.mu (reachesComm_body_implies_unfold body h)

/-! ## Progress Predicates -/

/-- A configuration is done if:
    1. The process is `skip`
    2. All endpoints have type `end_` -/
def Done (G : GEnv) (C : Config) : Prop :=
  C.proc = .skip ∧ ∀ e L, lookupG G e = some L → L = .end_

/-- A configuration can progress if it can take a step. -/
def CanProgress (C : Config) : Prop :=
  ∃ C', Step C C'

/-- A configuration is stuck if it is neither done nor can progress. -/
def Stuck (G : GEnv) (C : Config) : Prop :=
  ¬Done G C ∧ ¬CanProgress C

/-! ## Fairness -/

/-- A trace is fair if every message in a buffer is eventually consumed.

This captures the intuition that the communication medium is reliable
and messages don't get stuck forever. -/
def FairTrace (trace : List Config) : Prop :=
  ∀ i e v, ∀ hi : i < trace.length,
    v ∈ lookupBuf (trace.get ⟨i, hi⟩).bufs e →
    ∃ j, ∃ hj : j < trace.length, j > i ∧
      v ∉ lookupBuf (trace.get ⟨j, hj⟩).bufs e

/-- Messages are eventually delivered under fair execution. -/
def EventuallyDelivered (e : Edge) (v : Value) (trace : List Config) : Prop :=
  ∀ i, ∀ hi : i < trace.length,
    v ∈ lookupBuf (trace.get ⟨i, hi⟩).bufs e →
    ∃ j, ∃ hj : j < trace.length, j > i ∧
      v ∉ lookupBuf (trace.get ⟨j, hj⟩).bufs e

/-! ## Deadlock Freedom Theorem -/

/-- Main deadlock freedom theorem.

A well-typed configuration where all endpoints can reach communication
is either done or can progress.

**Proof strategy**:
1. Case split on whether process is skip
2. If not skip, use progress theorem to show step exists
3. If skip, check if all types are end_
4. If all end_, we're Done
5. If some type is not end_, use ReachesComm to show step exists

**Dependencies**:
- Requires `progress` theorem from Preservation.lean
- Uses ReachesComm to ensure types aren't stuck -/
theorem deadlock_free (C : Config) (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv)
    (hWT : WTConfigN n S G D C)
    (hReaches : ∀ e L, lookupG G e = some L → L ≠ .end_ → ReachesComm L) :
    Done G C ∨ CanProgress C := by
  sorry  -- Proof requires progress theorem

/-- Corollary: well-typed configurations with progressive types are never stuck. -/
theorem not_stuck (C : Config) (n : SessionId) (S : SEnv) (G : GEnv) (D : DEnv)
    (hWT : WTConfigN n S G D C)
    (hReaches : ∀ e L, lookupG G e = some L → L ≠ .end_ → ReachesComm L) :
    ¬Stuck G C := by
  intro ⟨hNotDone, hNoProgress⟩
  have h := deadlock_free C n S G D hWT hReaches
  cases h with
  | inl hDone => exact hNotDone hDone
  | inr hProg => exact hNoProgress hProg

/-! ## Session Isolation -/

/-- Get the session ID affected by a step, if applicable.
    Returns the session ID of the endpoint involved in communication steps,
    or the newly created session for newSession. -/
def stepSessionId (C : Config) : Option SessionId :=
  match C.proc with
  | .send k _ =>
    match lookupStr C.store k with
    | some (.chan e) => some e.sid
    | _ => none
  | .recv k _ =>
    match lookupStr C.store k with
    | some (.chan e) => some e.sid
    | _ => none
  | .select k _ =>
    match lookupStr C.store k with
    | some (.chan e) => some e.sid
    | _ => none
  | .branch k _ =>
    match lookupStr C.store k with
    | some (.chan e) => some e.sid
    | _ => none
  | .newSession _ _ _ => some C.nextSid
  | _ => none

/-- A step affects a specific session. -/
def affectsSession (C : Config) (sid : SessionId) : Prop :=
  stepSessionId C = some sid

/-- Sessions don't interfere with each other.

A step affecting session s₁ leaves session s₂'s buffers unchanged. -/
theorem session_isolation (C C' : Config) (s1 s2 : SessionId) (r : Role)
    (hNeq : s1 ≠ s2)
    (hStep : StepBase C C')
    (hAffects : affectsSession C s1) :
    ∀ ep : Endpoint, ep.sid = s2 →
      lookupBuf C.bufs { sid := ep.sid, sender := ep.role, receiver := r } =
      lookupBuf C'.bufs { sid := ep.sid, sender := ep.role, receiver := r } := by
  sorry  -- Proof by case analysis on hStep

/-- Disjoint sessions can be stepped independently.

If two configurations step and affect different sessions, they commute. -/
theorem disjoint_sessions_commute (C C₁ C₂ : Config) (s1 s2 : SessionId)
    (hNeq : s1 ≠ s2)
    (hStep1 : StepBase C C₁)
    (hAffects1 : affectsSession C s1)
    (hStep2 : StepBase C C₂)
    (hAffects2 : affectsSession C s2) :
    ∃ C', StepBase C₁ C' ∧ StepBase C₂ C' := by
  sorry  -- Proof requires showing steps commute

end
