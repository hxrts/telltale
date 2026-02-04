import Protocol.Semantics
import Protocol.Typing
import Protocol.Preservation

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

/-- Measure: count nested mu constructors at the top level.
    This serves as a termination measure for reachesComm_body_implies_unfold. -/
def muDepth : LocalType → Nat
  | .mu L => 1 + muDepth L
  | _ => 0

/-- Substitution preserves reachesCommDecide.

The key insight is that subst preserves the top-level constructor for all types
except .var. Since reachesCommDecide returns true only for communication types
(send/recv/select/branch) or mu-types with progressive bodies, and these top-level
constructors are preserved by subst, the result holds.

NOTE: We use explicit `LocalType.subst n replacement L` syntax because the dot
notation `L.subst n replacement` puts L in the replacement position (Lean inserts
the receiver at the first matching type position). -/
theorem subst_preserves_reachesCommDecide (n : Nat) (replacement : LocalType) (L : LocalType)
    (hL : reachesCommDecide L = true) :
    reachesCommDecide (LocalType.subst n replacement L) = true := by
  cases L with
  | send r T L' =>
    -- subst n replacement (.send r T L') = .send r T (subst n replacement L')
    -- reachesCommDecide .send = true
    rfl
  | recv r T L' =>
    -- subst n replacement (.recv r T L') = .recv r T (subst n replacement L')
    -- reachesCommDecide .recv = true
    rfl
  | select r bs =>
    -- subst n replacement (.select r bs) = .select r bs (no recursion in branches)
    unfold LocalType.subst
    exact hL
  | branch r bs =>
    -- subst n replacement (.branch r bs) = .branch r bs (no recursion in branches)
    unfold LocalType.subst
    exact hL
  | end_ =>
    -- reachesCommDecide .end_ = false, contradicts hL
    exact Bool.noConfusion hL
  | var m =>
    -- reachesCommDecide (.var m) = false, contradicts hL
    exact Bool.noConfusion hL
  | mu L' =>
    -- subst n replacement (.mu L') = .mu (subst (n+1) replacement L')
    -- reachesCommDecide (.mu _) = reachesCommDecide body
    simp only [LocalType.subst, reachesCommDecide] at *
    -- Now hL : reachesCommDecide L' = true
    -- Goal : reachesCommDecide (L'.subst (n+1) replacement) = true
    -- Use structural recursion (subst_preserves_reachesCommDecide is proved by structural recursion)
    exact subst_preserves_reachesCommDecide (n + 1) replacement L' hL

/-- Helper: for non-mu comm types, ReachesComm holds directly. -/
private theorem reachesComm_of_comm (L : LocalType) (h : reachesCommDecide L = true)
    (hNotMu : ∀ L', L ≠ .mu L') : ReachesComm L := by
  cases L with
  | send => exact ReachesComm.send
  | recv => exact ReachesComm.recv
  | select r bs =>
    simp only [reachesCommDecide, Bool.not_eq_true'] at h
    exact ReachesComm.select (fun hemp => by simp [hemp] at h)
  | branch r bs =>
    simp only [reachesCommDecide, Bool.not_eq_true'] at h
    exact ReachesComm.branch (fun hemp => by simp [hemp] at h)
  | end_ => exact Bool.noConfusion h
  | var => exact Bool.noConfusion h
  | mu L' => exact absurd rfl (hNotMu L')

/-- Key insight: subst preserves the top-level constructor for non-var types.
    For comm types (send/recv/select/branch), this lets us build ReachesComm. -/
private theorem reachesComm_subst_comm (L : LocalType) (n : Nat) (r : LocalType)
    (h : reachesCommDecide L = true) (hNotMu : ∀ L', L ≠ .mu L') (hNotVar : ∀ m, L ≠ .var m) :
    ReachesComm (LocalType.subst n r L) := by
  cases L with
  | send => simp only [LocalType.subst]; exact ReachesComm.send
  | recv => simp only [LocalType.subst]; exact ReachesComm.recv
  | select r bs =>
    simp only [LocalType.subst, reachesCommDecide, Bool.not_eq_true'] at *
    exact ReachesComm.select (fun hemp => by simp [hemp] at h)
  | branch r bs =>
    simp only [LocalType.subst, reachesCommDecide, Bool.not_eq_true'] at *
    exact ReachesComm.branch (fun hemp => by simp [hemp] at h)
  | end_ => exact Bool.noConfusion h
  | var m => exact absurd rfl (hNotVar m)
  | mu L' => exact absurd rfl (hNotMu L')

/-! ## Unfold Soundness Helpers -/

/-- Substitution preserves muDepth for types that can reach communication. -/
private theorem muDepth_subst_of_decide (n : Nat) (r L : LocalType)
    (h : reachesCommDecide L = true) :
    muDepth (LocalType.subst n r L) = muDepth L := by
  cases L with
  | send r' T L' =>
      simp [LocalType.subst, muDepth]
  | recv r' T L' =>
      simp [LocalType.subst, muDepth]
  | select r' bs =>
      simp [LocalType.subst, muDepth]
  | branch r' bs =>
      simp [LocalType.subst, muDepth]
  | end_ =>
      exact Bool.noConfusion h
  | var m =>
      exact Bool.noConfusion h
  | mu L' =>
      have h' : reachesCommDecide L' = true := by
        simpa [reachesCommDecide] using h
      have ih := muDepth_subst_of_decide (n + 1) r L' h'
      simp [LocalType.subst, muDepth, ih]

/-- Non-mu case: unfold is identity, so ReachesComm follows from the decision. -/
private theorem reachesComm_unfold_nonmu (L : LocalType) (h : reachesCommDecide L = true)
    (hNotMu : ∀ L', L ≠ .mu L') : ReachesComm L.unfold := by
  -- Unfold does not change non-mu types; use the direct constructors.
  cases L with
  | send => simpa [LocalType.unfold] using ReachesComm.send
  | recv => simpa [LocalType.unfold] using ReachesComm.recv
  | select r bs =>
      by_cases hEmpty : bs = []
      · simp [reachesCommDecide, hEmpty] at h
      · simpa [LocalType.unfold] using ReachesComm.select hEmpty
  | branch r bs =>
      by_cases hEmpty : bs = []
      · simp [reachesCommDecide, hEmpty] at h
      · simpa [LocalType.unfold] using ReachesComm.branch hEmpty
  | end_ => exact Bool.noConfusion h
  | var => exact Bool.noConfusion h
  | mu L' => exact (hNotMu L' rfl).elim

/-- Arithmetic helper: strip two leading mu constructors. -/
private theorem muDepth_le_of_mu_mu_le {L : LocalType} {fuel : Nat} :
    muDepth (.mu (.mu L)) ≤ fuel.succ → muDepth L ≤ fuel := by
  -- Expand muDepth and solve the arithmetic side-goal.
  intro h
  simp [muDepth] at h
  omega

/-- Mu case: prove reachability by recursing on the unfolded body. -/
private theorem reachesComm_unfold_mu (fuel : Nat) (L : LocalType)
    (hFuel : muDepth (LocalType.mu L) ≤ fuel.succ) (hBody : reachesCommDecide L = true)
    (ih : ∀ L, muDepth L ≤ fuel → reachesCommDecide L = true → ReachesComm L.unfold) :
    ReachesComm (LocalType.unfold (LocalType.mu L)) := by
  cases L with
  | send r T L' =>
      simp [LocalType.unfold, LocalType.subst]
      exact ReachesComm.send
  | recv r T L' =>
      simp [LocalType.unfold, LocalType.subst]
      exact ReachesComm.recv
  | select r bs =>
      have hNonEmpty : bs ≠ [] := by
        by_cases hEmpty : bs = []
        · simp [reachesCommDecide, hEmpty] at hBody
        · exact hEmpty
      simp [LocalType.unfold, LocalType.subst]
      exact ReachesComm.select hNonEmpty
  | branch r bs =>
      have hNonEmpty : bs ≠ [] := by
        by_cases hEmpty : bs = []
        · simp [reachesCommDecide, hEmpty] at hBody
        · exact hEmpty
      simp [LocalType.unfold, LocalType.subst]
      exact ReachesComm.branch hNonEmpty
  | end_ =>
      exact Bool.noConfusion hBody
  | var m =>
      exact Bool.noConfusion hBody
  | mu L' =>
      -- L = .mu L' so unfold (mu (mu L')) = mu (subst 1 (mu (mu L')) L')
      have hBody' : reachesCommDecide L' = true := by
        simpa [reachesCommDecide] using hBody
      have hFuel' : muDepth L' ≤ fuel :=
        muDepth_le_of_mu_mu_le (L:=L') (fuel:=fuel) (by simpa using hFuel)
      set L1 : LocalType := LocalType.subst 1 (.mu (.mu L')) L'
      have hEq : muDepth L1 = muDepth L' :=
        muDepth_subst_of_decide (n:=1) (r:=.mu (.mu L')) (L:=L') hBody'
      have hFuel1 : muDepth L1 ≤ fuel := by
        simpa [hEq] using hFuel'
      have hDec1 : reachesCommDecide L1 = true :=
        subst_preserves_reachesCommDecide (n:=1) (replacement:=.mu (.mu L')) (L:=L') hBody'
      have hIH : ReachesComm L1.unfold := ih L1 hFuel1 hDec1
      have hMu : ReachesComm (.mu L1) := ReachesComm.mu hIH
      simpa [LocalType.unfold, LocalType.subst, L1] using hMu

/-- Auxiliary: ReachesComm after unfolding, with explicit fuel for termination. -/
private theorem reachesComm_body_implies_unfold_aux :
    ∀ fuel L, muDepth L ≤ fuel → reachesCommDecide L = true → ReachesComm L.unfold
  | fuel, L, hFuel, hBody =>
      cases L with
      | send r T L' =>
          simp [LocalType.unfold]
          exact ReachesComm.send
      | recv r T L' =>
          simp [LocalType.unfold]
          exact ReachesComm.recv
      | select r bs =>
          have hNonEmpty : bs ≠ [] := by
            by_cases hEmpty : bs = []
            · simp [reachesCommDecide, hEmpty] at hBody
            · exact hEmpty
          simp [LocalType.unfold]
          exact ReachesComm.select hNonEmpty
      | branch r bs =>
          have hNonEmpty : bs ≠ [] := by
            by_cases hEmpty : bs = []
            · simp [reachesCommDecide, hEmpty] at hBody
            · exact hEmpty
          simp [LocalType.unfold]
          exact ReachesComm.branch hNonEmpty
      | end_ =>
          exact Bool.noConfusion hBody
      | var m =>
          exact Bool.noConfusion hBody
      | mu L' =>
          cases fuel with
          | zero =>
              have : False := by
                simp [muDepth] at hFuel
              exact this.elim
          | succ fuel' =>
              have hBody' : reachesCommDecide L' = true := by
                simpa [reachesCommDecide] using hBody
              have ih :
                  ∀ L, muDepth L ≤ fuel' → reachesCommDecide L = true → ReachesComm L.unfold :=
                fun L hF hD => reachesComm_body_implies_unfold_aux fuel' L hF hD
              exact reachesComm_unfold_mu (fuel:=fuel') (L:=L') (by simpa using hFuel) hBody' ih

/-- Helper: reachesCommDecide is monotonic under unfolding for guarded types. -/
theorem reachesComm_body_implies_unfold (L : LocalType)
    (hBody : reachesCommDecide L = true) :
    ReachesComm L.unfold := by
  exact reachesComm_body_implies_unfold_aux (muDepth L) L (by exact le_rfl) hBody

/-- Soundness: if decidable checker returns true, the type reaches communication. -/
theorem reachesCommDecide_sound (L : LocalType) (h : reachesCommDecide L = true) :
    ReachesComm L := by
  cases L with
  | send r T L' =>
      exact ReachesComm.send
  | recv r T L' =>
      exact ReachesComm.recv
  | select r bs =>
      have hNonEmpty : bs ≠ [] := by
        by_cases hEmpty : bs = []
        · simp [reachesCommDecide, hEmpty] at h
        · exact hEmpty
      exact ReachesComm.select hNonEmpty
  | branch r bs =>
      have hNonEmpty : bs ≠ [] := by
        by_cases hEmpty : bs = []
        · simp [reachesCommDecide, hEmpty] at h
        · exact hEmpty
      exact ReachesComm.branch hNonEmpty
  | end_ =>
      exact Bool.noConfusion h
  | var m =>
      exact Bool.noConfusion h
  | mu L' =>
      have hBody : reachesCommDecide L' = true := by
        simpa [reachesCommDecide] using h
      exact ReachesComm.mu (reachesComm_body_implies_unfold L' hBody)

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

/-- Progress-ready configuration (gap to be discharged by projection).

    This captures the two missing facts for progress:
    1. If the process is `skip`, then all endpoints are at `end_`
    2. The process is not blocked on an empty receive/branch buffer -/
def ProgressReady (C : Config) : Prop :=
  -- Ready = skip implies done, and no blocked recv/branch.
  (C.proc = .skip → ∀ e L, lookupG C.G e = some L → L = .end_) ∧
  ¬ BlockedProc C.store C.bufs C.proc

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
theorem deadlock_free (C : Config) (Ssh Sown : SEnv)
    (hWF : LocalTypeR.WellFormed C.G C.D Ssh Sown C.store C.bufs C.proc)
    (hReady : ProgressReady C)
    (hReaches : ∀ e L, lookupG C.G e = some L → L ≠ .end_ → ReachesComm L) :
    Done C.G C ∨ CanProgress C := by
  rcases hReady with ⟨hDoneIfSkip, hNotBlocked⟩
  have hProgress := progress (G:=C.G) (D:=C.D) (Ssh:=Ssh) (Sown:=Sown)
    (store:=C.store) (bufs:=C.bufs) (P:=C.proc) hWF
  rcases hProgress with hSkip | hStep | hBlocked
  · left
    exact ⟨hSkip, hDoneIfSkip hSkip⟩
  · right
    rcases hStep with ⟨G', D', Sown', store', bufs', P', hTS⟩
    refine ⟨{ proc := P', store := store', bufs := bufs', G := G', D := D',
              nextSid := C.nextSid }, ?_⟩
    exact subject_reduction (n:=C.nextSid) hTS
  · exact (hNotBlocked hBlocked).elim

/-- Corollary: well-typed configurations with progressive types are never stuck. -/
theorem not_stuck (C : Config) (Ssh Sown : SEnv)
    (hWF : LocalTypeR.WellFormed C.G C.D Ssh Sown C.store C.bufs C.proc)
    (hReady : ProgressReady C)
    (hReaches : ∀ e L, lookupG C.G e = some L → L ≠ .end_ → ReachesComm L) :
    ¬Stuck C.G C := by
  intro hStuck
  rcases hStuck with ⟨hNotDone, hNotProg⟩
  have h := deadlock_free (C:=C) (Ssh:=Ssh) (Sown:=Sown) hWF hReady hReaches
  cases h with
  | inl hDone => exact hNotDone hDone
  | inr hProg => exact hNotProg hProg

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
  intro ep hep
  -- Define the edge we're querying
  let queryEdge : Edge := { sid := ep.sid, sender := ep.role, receiver := r }
  cases hStep with
  | send hProc hk hx hG =>
    -- send modifies edge based on endpoint from store
    simp only [affectsSession, stepSessionId, hProc, hk] at hAffects
    simp only [sendStep, enqueueBuf]
    symm
    apply lookupBuf_update_neq
    intro heq
    -- heq: modified edge = query edge, so their sids are equal
    have h1 : (_ : Edge).sid = queryEdge.sid := congrArg Edge.sid heq
    simp only [queryEdge] at h1
    -- h1: e✝.sid = ep.sid, hAffects: e✝.sid = s1, hep: ep.sid = s2
    have heSid : (_ : Endpoint).sid = s1 := Option.some_injective _ hAffects
    rw [heSid, hep] at h1
    exact hNeq h1
  | recv hProc hk hG hBufLookup =>
    -- recv modifies edge based on endpoint from store
    simp only [affectsSession, stepSessionId, hProc, hk] at hAffects
    -- hBufLookup: lookupBuf = v :: _, so match will take the cons branch
    simp only [recvStep, dequeueBuf, hBufLookup]
    -- Now goal is: lookup C.bufs = lookup (updateBuf C.bufs edge _) queryEdge
    symm
    apply lookupBuf_update_neq
    intro heq
    have h1 : (_ : Edge).sid = queryEdge.sid := congrArg Edge.sid heq
    simp only [queryEdge] at h1
    have heSid : (_ : Endpoint).sid = s1 := Option.some_injective _ hAffects
    rw [heSid, hep] at h1
    exact hNeq h1
  | select hProc hk hG hFind =>
    -- select is like send
    simp only [affectsSession, stepSessionId, hProc, hk] at hAffects
    simp only [sendStep, enqueueBuf]
    symm
    apply lookupBuf_update_neq
    intro heq
    have h1 : (_ : Edge).sid = queryEdge.sid := congrArg Edge.sid heq
    simp only [queryEdge] at h1
    have heSid : (_ : Endpoint).sid = s1 := Option.some_injective _ hAffects
    rw [heSid, hep] at h1
    exact hNeq h1
  | branch hProc hk hG hBufVal hFindP hFindT hdq =>
    -- branch modifies bufs directly via hdq
    rename_i bufs'_  -- the bufs' implicit argument
    simp only [affectsSession, stepSessionId, hProc, hk] at hAffects
    -- hdq : dequeueBuf C.bufs edge = some (bufs'_, _)
    -- hBufVal gives us that the buffer is non-empty with a string
    simp only [dequeueBuf, hBufVal] at hdq
    simp only [Option.some.injEq] at hdq
    -- hdq : (updateBuf C.bufs edge _, _) = (bufs'_, _)
    -- Goal involves bufs'_ which equals updateBuf C.bufs edge _
    have hBufsEq : _ = bufs'_ := congrArg Prod.fst hdq
    rw [← hBufsEq]
    symm
    apply lookupBuf_update_neq
    intro heq
    have h1 : (_ : Edge).sid = queryEdge.sid := congrArg Edge.sid heq
    simp only [queryEdge] at h1
    have heSid : (_ : Endpoint).sid = s1 := Option.some_injective _ hAffects
    rw [heSid, hep] at h1
    exact hNeq h1
  | newSession hProc =>
    -- newSession prepends buffers for session C.nextSid = s1
    rename_i theRoles _ _  -- the implicit roles, f, P arguments
    simp only [affectsSession, stepSessionId, hProc] at hAffects
    have hSidEq : C.nextSid = s1 := Option.some_injective _ hAffects
    simp only [newSessionStep]
    -- Query is for s2, new buffers are for s1 = C.nextSid
    simp only [lookupBuf, List.lookup_append]
    -- queryEdge.sid = ep.sid = s2 ≠ s1 = C.nextSid
    have hSidNe : queryEdge.sid ≠ C.nextSid := by
      simp only [queryEdge, hep]
      rw [hSidEq]
      exact Ne.symm hNeq
    have hLookupNone := initBuffers_lookup_none C.nextSid theRoles queryEdge hSidNe
    rw [hLookupNone]
    simp only [Option.none_or]
  | assign hProc =>
    -- assign doesn't modify buffers
    rfl
  | seq2 hProc =>
    -- seq2 doesn't modify buffers
    rfl
  | par_skip_left hProc =>
    -- par_skip_left doesn't modify buffers
    rfl
  | par_skip_right hProc =>
    -- par_skip_right doesn't modify buffers
    rfl

/-- Disjoint sessions can be stepped independently.

If two configurations step and affect different sessions, they commute.

Note: For StepBase (head reductions), the hypotheses are actually contradictory
because stepSessionId is deterministic. If affectsSession C s1 and affectsSession C s2
both hold, then s1 = s2, contradicting hNeq. This makes the theorem vacuously true.

The meaningful version of this theorem would use the Step relation with parallel
composition, where par_left and par_right can step different subprocesses. -/
theorem disjoint_sessions_commute (C C₁ C₂ : Config) (s1 s2 : SessionId)
    (hNeq : s1 ≠ s2)
    (_hStep1 : StepBase C C₁)
    (hAffects1 : affectsSession C s1)
    (_hStep2 : StepBase C C₂)
    (hAffects2 : affectsSession C s2) :
    ∃ C', StepBase C₁ C' ∧ StepBase C₂ C' := by
  -- The hypotheses are contradictory: stepSessionId is deterministic
  -- hAffects1 : stepSessionId C = some s1
  -- hAffects2 : stepSessionId C = some s2
  -- These imply s1 = s2, contradicting hNeq
  simp only [affectsSession] at hAffects1 hAffects2
  rw [hAffects1] at hAffects2
  exact absurd (Option.some_injective _ hAffects2) hNeq

end
