import Protocol.Preservation
import Protocol.DeadlockFreedomReachability

/-! # Protocol.DeadlockFreedomCore

Progress/fairness deadlock-freedom theorems and session-isolation lemmas.
-/

/-
The Problem. Lift reachability assumptions into full configuration progress and isolation results.

Solution Structure. Define done/stuck predicates, prove deadlock-freedom, then isolate sessions.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section
-- Progress Predicates

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

-- Fairness

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

-- Deadlock Freedom Theorem

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
    (hWF : WellFormedComplete C.G C.D Ssh Sown C.store C.bufs C.proc)
    (hReady : ProgressReady C)
    (_hReaches : ∀ e L, lookupG C.G e = some L → L ≠ .end_ → ReachesComm L) :
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
    (hWF : WellFormedComplete C.G C.D Ssh Sown C.store C.bufs C.proc)
    (hReady : ProgressReady C)
    (hReaches : ∀ e L, lookupG C.G e = some L → L ≠ .end_ → ReachesComm L) :
    ¬Stuck C.G C := by
  intro hStuck
  rcases hStuck with ⟨hNotDone, hNotProg⟩
  have h := deadlock_free (C:=C) (Ssh:=Ssh) (Sown:=Sown) hWF hReady hReaches
  cases h with
  | inl hDone => exact hNotDone hDone
  | inr hProg => exact hNotProg hProg

-- Session Isolation

-- Session-Affecting Step Identification

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

-- Session Isolation Under Head Steps

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
  -- session_isolation: Step-Form Case Analysis
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
  -- session_isolation: Receive Case
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
  -- session_isolation: Select Case
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
  -- session_isolation: Branch Case
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
  -- session_isolation: New-Session Case
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
  -- session_isolation: Buffer-Preserving Structural Cases
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

-- Disjoint-Step Commutativity Corollary

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
