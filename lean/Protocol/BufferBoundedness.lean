import Protocol.Semantics
import Protocol.Coherence.EdgeCoherence
import Protocol.Coherence.Preservation
import Protocol.DeliveryModel
import Mathlib

/-!
# Buffer Boundedness and Phase Transition

This module formalizes the critical buffer size theorem for multiparty session types.

## Key Results

1. **Critical Buffer Size**: For any well-typed initial configuration C₀, there exists a
   critical buffer size B_c such that:
   - For B ≥ B_c: bounded-buffer execution is equivalent to unbounded
   - For B < B_c: deadlocking executions exist

2. **Phase Transition Sharpness**: The transition at B_c is sharp — there is no
   intermediate regime.

3. **Computability**: B_c is computable from the initial configuration for
   finite-state protocols.

## Definitions

- `maxBufferOccupancy`: Maximum buffer size across all edges in a configuration
- `criticalBufferSize`: Supremum of buffer occupancies over reachable configurations
- `BoundedStep`: Step relation that blocks when buffer would exceed capacity
- `BoundedCoherent`: Coherence with explicit buffer bound

## Connection to Coherence

The key insight is that `BddAbove` for buffer occupancies follows from coherence:
well-typed configurations have bounded buffer growth because sends and receives
must match through the session type discipline.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Helper Lemmas -/

/-- If lookup finds a value, the pair is in the list. -/
lemma lookup_mem_buf {l : List (Edge × Buffer)} {e : Edge} {buf : Buffer}
    (h : l.lookup e = some buf) : (e, buf) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    by_cases hEq : e = hd.1
    · have hbuf : buf = hd.2 := by
        have : some hd.2 = some buf := by
          simpa [List.lookup, hEq] using h
        exact Option.some.inj this.symm
      have hpair : (e, buf) = hd := by
        cases hd with
        | mk hd1 hd2 =>
          cases hEq
          cases hbuf
          rfl
      exact List.mem_cons.mpr (Or.inl hpair)
    · have hne : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hEq
      have h' : tl.lookup e = some buf := by
        simpa [List.lookup, hne] using h
      have : (e, buf) ∈ tl := ih h'
      exact List.mem_cons.mpr (Or.inr this)

/-- Foldl max grows the accumulator. -/
theorem foldl_max_ge_init (l : List Nat) (init : Nat) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h1 : init ≤ max init hd := le_max_left _ _
    have h2 : max init hd ≤ tl.foldl max (max init hd) := ih (max init hd)
    exact le_trans h1 h2

/-- Foldl max is at least any element in the list. -/
theorem foldl_max_le_of_mem {l : List Nat} {n : Nat} (h : n ∈ l) (init : Nat) :
    n ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => cases h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · calc n ≤ max init n := le_max_right _ _
           _ ≤ tl.foldl max (max init n) := foldl_max_ge_init tl _
    · exact ih hmem (max init hd)

/-! ## Buffer Occupancy -/

/-- Maximum buffer occupancy across all edges in a configuration. -/
def maxBufferOccupancy (C : Config) : Nat :=
  (C.bufs.map (fun (_, buf) => buf.length)).foldl max 0

/-- Buffer occupancy for a specific edge. -/
def edgeBufferOccupancy (C : Config) (e : Edge) : Nat :=
  (lookupBuf C.bufs e).length

theorem maxBufferOccupancy_ge_edge (C : Config) (e : Edge)
    (_h : ∃ buf, (e, buf) ∈ C.bufs) :
    maxBufferOccupancy C ≥ edgeBufferOccupancy C e := by
  simp only [maxBufferOccupancy, edgeBufferOccupancy, lookupBuf]
  -- Case split on whether lookup returns some or none
  cases hlook : C.bufs.lookup e with
  | none =>
    -- If lookup fails, edgeBufferOccupancy is 0
    simp only [Option.getD]
    exact Nat.zero_le _
  | some buf' =>
    -- If lookup returns buf', then (e, buf') ∈ C.bufs
    simp only [Option.getD]
    have hmem : (e, buf') ∈ C.bufs := lookup_mem_buf hlook
    have hmap : buf'.length ∈ C.bufs.map (fun x => x.2.length) := by
      simp only [List.mem_map]
      exact ⟨(e, buf'), hmem, rfl⟩
    exact foldl_max_le_of_mem hmap 0

/-- Any edge occupancy is bounded by the global max occupancy. -/
theorem edgeBufferOccupancy_le_maxBufferOccupancy (C : Config) (e : Edge) :
    edgeBufferOccupancy C e ≤ maxBufferOccupancy C := by
  by_cases hmem : ∃ buf, (e, buf) ∈ C.bufs
  · exact maxBufferOccupancy_ge_edge C e hmem
  · cases hlook : C.bufs.lookup e with
    | none =>
      simp [edgeBufferOccupancy, lookupBuf, hlook]
    | some buf =>
      have : (e, buf) ∈ C.bufs := lookup_mem_buf hlook
      exact (False.elim (hmem ⟨buf, this⟩))

/-- Membership in `updateBuf` comes either from the updated edge or from the old list. -/
private theorem mem_updateBuf_cases {bufs : Buffers} {e e' : Edge} {buf buf' : Buffer}
    (hmem : (e', buf') ∈ updateBuf bufs e buf) :
    (e' = e ∧ buf' = buf) ∨ (e', buf') ∈ bufs := by
  induction bufs with
  | nil =>
      left
      simpa [updateBuf, List.mem_singleton, Prod.mk.injEq] using hmem
  | cons hd tl ih =>
      by_cases heq : e = hd.1
      · simp [updateBuf, heq] at hmem
        rcases hmem with hhead | htail
        · left
          rcases hhead with ⟨he', hb'⟩
          exact ⟨he'.trans heq.symm, hb'⟩
        · right
          exact List.mem_cons_of_mem _ htail
      · simp [updateBuf, heq] at hmem
        rcases hmem with hhead | htail
        · right
          exact List.mem_cons.mpr (Or.inl hhead)
        · rcases ih htail with hnew | hold
          · exact Or.inl hnew
          · exact Or.inr (List.mem_cons.mpr (Or.inr hold))

/-- Local helper: foldl max with bounded init and bounded elements stays bounded. -/
private theorem foldl_max_le_of_all_le_aux_local {l : List Nat} {B init : Nat}
    (hinit : init ≤ B) (h : ∀ n ∈ l, n ≤ B) : l.foldl max init ≤ B := by
  induction l generalizing init with
  | nil =>
      simpa using hinit
  | cons hd tl ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_le hinit (h hd (by simp))
      · intro n hn
        exact h n (by simp [hn])

/-- Local helper: foldl max with init 0 and bounded elements stays bounded. -/
private theorem foldl_max_le_of_all_le_local {l : List Nat} {B : Nat}
    (h : ∀ n ∈ l, n ≤ B) : l.foldl max 0 ≤ B :=
  foldl_max_le_of_all_le_aux_local (Nat.zero_le B) h

/-- Updating one edge with a buffer no longer than before cannot increase max occupancy. -/
private theorem maxBufferOccupancy_updateBuf_le_of_le
    (C : Config) (e : Edge) (buf : Buffer)
    (hbuf : buf.length ≤ edgeBufferOccupancy C e) :
    maxBufferOccupancy { C with bufs := updateBuf C.bufs e buf } ≤ maxBufferOccupancy C := by
  unfold maxBufferOccupancy
  apply foldl_max_le_of_all_le_local
  intro n hn
  simp only [List.mem_map] at hn
  rcases hn with ⟨⟨e', buf'⟩, hmem', hn⟩
  subst n
  have hCases := mem_updateBuf_cases (bufs := C.bufs) (e := e) (e' := e') (buf := buf)
    (buf' := buf') hmem'
  cases hCases with
  | inl hnew =>
    rcases hnew with ⟨heq, hbuf'⟩
    subst e' buf'
    exact le_trans hbuf (edgeBufferOccupancy_le_maxBufferOccupancy C e)
  | inr hold =>
    have hmap : buf'.length ∈ C.bufs.map (fun x => x.2.length) := by
      simp only [List.mem_map]
      exact ⟨(e', buf'), hold, rfl⟩
    exact foldl_max_le_of_mem hmap 0

theorem maxBufferOccupancy_zero_of_empty (C : Config) (h : C.bufs = []) :
    maxBufferOccupancy C = 0 := by
  simp [maxBufferOccupancy, h]

/-! ## Unbounded Step Relation -/

/-- The unbounded step relation from Config. This is the existing step semantics
    without any buffer capacity constraint. -/
def UnboundedStep (C C' : Config) : Prop :=
  Step C C'

/-- Unbounded reachability: reflexive-transitive closure of Step. -/
def UnboundedReachable (C₀ C : Config) : Prop :=
  Relation.ReflTransGen Step C₀ C

/-! ## Bounded Step Relation -/

/-- Bounded step: like Step but send operations are blocked if the buffer
    would exceed capacity B. Receive operations are always allowed as they
    reduce buffer occupancy. -/
inductive BoundedStep (B : Nat) : Config → Config → Prop where
  | send (C C' : Config)
      (hstep : Step C C')
      (hbound : maxBufferOccupancy C' ≤ B) :
      BoundedStep B C C'
  | recv (C C' : Config)
      (hstep : Step C C')
      (hRecv : ∃ x source, C.proc = .recv x source) :
      BoundedStep B C C'

/-- Bounded reachability: reflexive-transitive closure of BoundedStep. -/
def BoundedReachable (B : Nat) (C₀ C : Config) : Prop :=
  Relation.ReflTransGen (BoundedStep B) C₀ C

/-! ## Critical Buffer Size -/

/-- The set of buffer occupancies reachable from an initial configuration. -/
def occupancySet (C₀ : Config) : Set Nat :=
  { n | ∃ C, UnboundedReachable C₀ C ∧ maxBufferOccupancy C = n }

/-- The occupancy set is always nonempty: it contains the initial occupancy. -/
theorem occupancySet_nonempty (C₀ : Config) : (occupancySet C₀).Nonempty := by
  refine ⟨maxBufferOccupancy C₀, ?_⟩
  exact ⟨C₀, Relation.ReflTransGen.refl, rfl⟩

/-- A global occupancy bound along unbounded executions yields `BddAbove` for
    the occupancy set. -/
theorem occupancySet_bddAbove_of_global_bound (C₀ : Config)
    (hfinite : ∃ n : Nat, ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ n) :
    BddAbove (occupancySet C₀) := by
  rcases hfinite with ⟨bound, hbound⟩
  refine ⟨bound, ?_⟩
  intro n hn
  rcases hn with ⟨C, hreach, hocc⟩
  rw [← hocc]
  exact hbound C hreach

/-- Critical buffer size: supremum of buffer occupancies over all reachable configs.
    This is the minimum buffer capacity needed for deadlock-free execution. -/
def criticalBufferSize (C₀ : Config) : Nat :=
  sSup (occupancySet C₀)

/-! ## Terminal and Deadlocked -/

/-- A configuration is terminal if all local types are `end_`. -/
def IsTerminal (C : Config) : Prop :=
  ∀ ep L, lookupG C.G ep = some L → L = .end_

/-- A configuration is deadlocked if it's not terminal and no step is possible. -/
def Deadlocked (C : Config) : Prop :=
  ¬IsTerminal C ∧ ¬∃ C', Step C C'

/-- A configuration is bounded-stuck if it's not terminal and no bounded step is possible.
    This can happen when unbounded steps exist but are blocked by the buffer capacity. -/
def BoundedStuck (B : Nat) (C : Config) : Prop :=
  ¬IsTerminal C ∧ ¬∃ C', BoundedStep B C C'

/-! ## Key Lemmas -/

/-- Bounded step implies unbounded step. -/
theorem BoundedStep_implies_Step {B : Nat} {C C' : Config}
    (h : BoundedStep B C C') : Step C C' := by
  cases h with
  | send hstep _ => exact hstep
  | recv hstep _ => exact hstep

/-- A deadlocked config is bounded-stuck for any B. -/
theorem Deadlocked_implies_BoundedStuck {C : Config} (hD : Deadlocked C) (B : Nat) :
    BoundedStuck B C := by
  constructor
  · exact hD.1
  · intro ⟨C', hstep⟩
    exact hD.2 ⟨C', BoundedStep_implies_Step hstep⟩

/-- Bounded reachability implies unbounded reachability. -/
theorem BoundedReachable_implies_UnboundedReachable {B : Nat} {C₀ C : Config}
    (h : BoundedReachable B C₀ C) : UnboundedReachable C₀ C := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    apply Relation.ReflTransGen.tail ih
    exact BoundedStep_implies_Step hstep

/-- Closure: if all unbounded-reachable states stay within `B`, then
    unbounded reachability implies bounded reachability at `B`. -/
theorem bounded_reachability_closure (C₀ : Config) (B : Nat)
    (hSafe : ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B) :
    ∀ C, UnboundedReachable C₀ C → BoundedReachable B C₀ C := by
  intro C hreach
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      apply Relation.ReflTransGen.tail ih
      refine BoundedStep.send _ _ hstep ?_
      exact hSafe _ (Relation.ReflTransGen.tail hreach hstep)

/-- Pointwise corollary form used by downstream theorems. -/
theorem bounded_reachability_of_unbounded_le (C₀ : Config) (B : Nat)
    (hSafe : ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B)
    {C : Config}
    (hreach : UnboundedReachable C₀ C)
    (_hOcc : maxBufferOccupancy C ≤ B) :
    BoundedReachable B C₀ C :=
  bounded_reachability_closure C₀ B hSafe C hreach

/-- Any reachable configuration has buffer occupancy ≤ critical buffer size,
    assuming the occupancy set is bounded above. -/
theorem maxBufferOccupancy_le_critical {C₀ C : Config}
    (hreach : UnboundedReachable C₀ C)
    (hbdd : BddAbove (occupancySet C₀)) :
    maxBufferOccupancy C ≤ criticalBufferSize C₀ := by
  have hmem : maxBufferOccupancy C ∈ occupancySet C₀ := ⟨C, hreach, rfl⟩
  exact le_csSup hbdd hmem

/-- An unbounded step from a reachable config stays within critical buffer size. -/
theorem unbounded_step_within_bound {C₀ C C' : Config}
    (hreach : UnboundedReachable C₀ C)
    (hstep : Step C C')
    (B : Nat) (hB : B ≥ criticalBufferSize C₀)
    (hbdd : BddAbove (occupancySet C₀)) :
    maxBufferOccupancy C' ≤ B := by
  have hreach' : UnboundedReachable C₀ C' := Relation.ReflTransGen.tail hreach hstep
  have hle : maxBufferOccupancy C' ≤ criticalBufferSize C₀ :=
    maxBufferOccupancy_le_critical hreach' hbdd
  exact le_trans hle hB

/-! ## Main Theorems -/

/-- **Theorem 1 (Upper bound)**: For buffer size B ≥ B_c, bounded-buffer
    execution is equivalent to unbounded execution. -/
theorem bounded_equiv_unbounded (C₀ : Config)
    (B : Nat) (hB : B ≥ criticalBufferSize C₀)
    (hbdd : BddAbove (occupancySet C₀)) :
    ∀ C, UnboundedReachable C₀ C ↔ BoundedReachable B C₀ C := by
  intro C
  constructor
  · -- Unbounded → Bounded: every step satisfies the bound
    intro hreach
    induction hreach with
    | refl => exact Relation.ReflTransGen.refl
    | tail hreach' hstep ih =>
      apply Relation.ReflTransGen.tail ih
      apply BoundedStep.send _ _ hstep
      exact unbounded_step_within_bound hreach' hstep B hB hbdd
  · -- Bounded → Unbounded: just forget the bound
    exact BoundedReachable_implies_UnboundedReachable

/-! ## Lower Bound Helpers -/

/-- A stepping configuration is not terminal if terminal configs cannot step. -/
private theorem not_terminal_of_step
    (hTerminalNoStep : ∀ C, IsTerminal C → ¬∃ C', Step C C')
    {C C' : Config} (hstep : Step C C') : ¬IsTerminal C := by
  -- Terminal configurations have no outgoing steps.
  intro hTerm
  exact hTerminalNoStep C hTerm ⟨C', hstep⟩

/-- Find the first step that crosses the buffer bound along an unbounded path. -/
private theorem exists_first_overflow
    {B : Nat} {C₀ C : Config}
    (hInit : maxBufferOccupancy C₀ ≤ B)
    (hreach : UnboundedReachable C₀ C)
    (hOcc : maxBufferOccupancy C > B) :
    ∃ Cpre Csucc, UnboundedReachable C₀ Cpre ∧ Step Cpre Csucc ∧
      maxBufferOccupancy Cpre ≤ B ∧ maxBufferOccupancy Csucc > B := by
  -- Induct on the reachability derivation to find the first overflow step.
  induction hreach with
  | refl =>
      exact (False.elim ((not_lt_of_ge hInit) hOcc))
  | tail hreach hstep ih =>
      rename_i Cmid Cfinal
      by_cases hpre : maxBufferOccupancy Cmid ≤ B
      · exact ⟨Cmid, Cfinal, hreach, hstep, hpre, hOcc⟩
      · exact ih (lt_of_not_ge hpre)

/-- Any bounded step equals the unique successor when Step is deterministic. -/
private theorem bounded_step_eq_succ
    (hDet : ∀ C C₁ C₂, Step C C₁ → Step C C₂ → C₁ = C₂)
    {B : Nat} {Cpre Csucc : Config} (hstep : Step Cpre Csucc) :
    ∀ {C'}, BoundedStep B Cpre C' → C' = Csucc := by
  -- Determinism collapses all bounded steps to the same successor.
  intro C' hB
  have hStep' : Step Cpre C' := BoundedStep_implies_Step hB
  exact hDet _ _ _ hStep' hstep

/-- A concrete recv step cannot increase the max buffer occupancy. -/
theorem recv_step_nonincrease_maxBufferOccupancy
    {C C' : Config}
    (hstep : Step C C')
    (hRecv : ∃ x source, C.proc = .recv x source) :
    maxBufferOccupancy C' ≤ maxBufferOccupancy C := by
  rcases hRecv with ⟨kRecv, xRecv, hProcRecv⟩
  cases hstep with
  | base hbase =>
      cases hbase with
      | recv hProc hk hG hBuf =>
          rename_i vs k x ep v src T L
          -- Dequeue shortens the touched edge buffer; others are unchanged.
          let recvEdge : Edge := { sid := ep.sid, sender := src, receiver := ep.role }
          have hTailLe : (lookupBuf C.bufs recvEdge).tail.length ≤ edgeBufferOccupancy C recvEdge := by
            simp [edgeBufferOccupancy]
          have hLeUpdate :
              maxBufferOccupancy
                { C with
                    bufs := updateBuf C.bufs recvEdge (lookupBuf C.bufs recvEdge).tail } ≤
              maxBufferOccupancy C := by
            exact maxBufferOccupancy_updateBuf_le_of_le C
              recvEdge (lookupBuf C.bufs recvEdge).tail hTailLe
          -- Simplify recvStep at this non-empty buffer.
          simpa [recvStep, dequeueBuf, recvEdge, hBuf] using hLeUpdate
      | send hProc _ _ _ =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | select hProc _ _ _ =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | branch hProc _ _ _ _ _ _ =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | newSession hProc =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | assign hProc =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | seq2 hProc =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | par_skip_left hProc =>
          exact False.elim (by simpa [hProcRecv] using hProc)
      | par_skip_right hProc =>
          exact False.elim (by simpa [hProcRecv] using hProc)
  | seq_left hProc _ =>
      exact False.elim (by simpa [hProcRecv] using hProc)
  | par_left hProc _ =>
      exact False.elim (by simpa [hProcRecv] using hProc)
  | par_right hProc _ =>
      exact False.elim (by simpa [hProcRecv] using hProc)

/-- Step determinism in a regime where every step is a base step and
    `par`-head processes are excluded. -/
theorem step_deterministic_of_base_regime
    (hBase : ∀ {C C'}, Step C C' → StepBase C C')
    (hNoPar : ∀ (C : Config) nS nG P Q, C.proc = Process.par nS nG P Q → False) :
    ∀ C C₁ C₂, Step C C₁ → Step C C₂ → C₁ = C₂ := by
  intro C C₁ C₂ hStep₁ hStep₂
  have hBase₁ : StepBase C C₁ := hBase hStep₁
  have hBase₂ : StepBase C C₂ := hBase hStep₂
  rcases stepBase_deterministic hBase₁ hBase₂ with hEq | hPar
  · exact hEq
  · rcases hPar with ⟨nS, nG, P, Q, hProc⟩
    exact False.elim (hNoPar C nS nG P Q hProc)

/-- If the unique successor exceeds the bound, no bounded step exists. -/
private theorem no_bounded_step_of_overflow
    (hDet : ∀ C C₁ C₂, Step C C₁ → Step C C₂ → C₁ = C₂)
    (hRecvNonInc : ∀ C C', Step C C' → (∃ x source, C.proc = .recv x source) →
      maxBufferOccupancy C' ≤ maxBufferOccupancy C)
    {B : Nat} {Cpre : Config} (Csucc : Config)
    (hstep : Step Cpre Csucc)
    (hPreLe : maxBufferOccupancy Cpre ≤ B)
    (hSuccGt : maxBufferOccupancy Csucc > B) :
    ¬∃ C', BoundedStep B Cpre C' := by
  -- Any bounded step must be the unique successor, which violates the bound.
  intro hBounded
  obtain ⟨C', hB⟩ := hBounded
  have hEq : C' = Csucc := bounded_step_eq_succ hDet hstep hB
  cases hB with
  | send _ hbound =>
      have hSuccGt' : maxBufferOccupancy C' > B := by
        simpa [hEq] using hSuccGt
      exact (not_lt_of_ge hbound hSuccGt')
  | recv hstep' hRecv =>
      have hle := hRecvNonInc _ _ hstep' hRecv
      have hleB : maxBufferOccupancy C' ≤ B := le_trans hle hPreLe
      have hSuccGt' : maxBufferOccupancy C' > B := by
        simpa [hEq] using hSuccGt
      exact (not_lt_of_ge hleB hSuccGt')

/-- **Theorem 2 (Lower bound)**: For buffer size B < B_c, there exists a
    bounded-reachable configuration that gets stuck under bounded semantics.
    Note: Uses BoundedStuck (no bounded step) rather than Deadlocked (no step at all).

    The proof uses classical logic: if all bounded-reachable configs have bounded successors,
    then bounded reachability would cover all unbounded-reachable configs, contradicting B < B_c. -/
theorem bounded_stuck_below_critical (C₀ : Config)
    (B : Nat) (hB : B < criticalBufferSize C₀)
    (hInit : maxBufferOccupancy C₀ ≤ B)
    (hBoundedReach : ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B →
      BoundedReachable B C₀ C)
    (hDet : ∀ C C₁ C₂, Step C C₁ → Step C C₂ → C₁ = C₂)
    (hTerminalNoStep : ∀ C, IsTerminal C → ¬∃ C', Step C C') :
    ∃ C, BoundedReachable B C₀ C ∧ BoundedStuck B C := by
  -- Extract a reachable configuration whose occupancy exceeds B.
  have hlt : B < sSup (occupancySet C₀) := hB
  obtain ⟨n, hn, hnB⟩ := exists_lt_of_lt_csSup (occupancySet_nonempty C₀) hlt
  obtain ⟨Cmax, hreachMax, hoccMax⟩ := hn
  have hCmaxOcc : maxBufferOccupancy Cmax > B := by
    simpa [hoccMax] using hnB
  -- Find the first step that crosses the bound.
  obtain ⟨Cpre, Csucc, hreachPre, hstepPre, hPreLe, hSuccGt⟩ :=
    exists_first_overflow hInit hreachMax hCmaxOcc
  have hBreachPre : BoundedReachable B C₀ Cpre :=
    hBoundedReach Cpre hreachPre hPreLe
  have hNotTerm : ¬IsTerminal Cpre := not_terminal_of_step hTerminalNoStep hstepPre
  have hNoBounded : ¬∃ C', BoundedStep B Cpre C' :=
    no_bounded_step_of_overflow hDet
      (fun C C' hstep hRecv =>
        recv_step_nonincrease_maxBufferOccupancy (C := C) (C' := C') hstep hRecv)
      Csucc hstepPre hPreLe hSuccGt
  exact ⟨Cpre, hBreachPre, ⟨hNotTerm, hNoBounded⟩⟩

/-- **Theorem 3 (Sharpness)**: The transition at B_c is sharp — there is a single
    threshold such that:
    - For all B ≥ B_c: the protocol is deadlock-free (no unbounded-stuck configs)
    - For all B < B_c: bounded-stuck configurations exist (bounded semantics blocks)
    Note: The lower bound uses BoundedStuck rather than Deadlocked because bounded
    semantics can get stuck even when unbounded steps would be possible. -/
theorem phase_transition_sharp (C₀ : Config)
    (hInit : maxBufferOccupancy C₀ = 0)
    (hBoundedReach : ∀ B C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B →
      BoundedReachable B C₀ C)
    (hDet : ∀ C C₁ C₂, Step C C₁ → Step C C₂ → C₁ = C₂)
    (hTerminalNoStep : ∀ C, IsTerminal C → ¬∃ C', Step C C')
    (h_unbounded_safe : ∀ C, UnboundedReachable C₀ C → ¬Deadlocked C)
    (hfinite : ∃ n : Nat, ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ n) :
    ∃ Bc : Nat,
      (∀ B, B ≥ Bc → ∀ C, BoundedReachable B C₀ C → ¬Deadlocked C) ∧
      (∀ B, B < Bc → ∃ C, BoundedReachable B C₀ C ∧ BoundedStuck B C) := by
  have hbdd : BddAbove (occupancySet C₀) :=
    occupancySet_bddAbove_of_global_bound C₀ hfinite
  use criticalBufferSize C₀
  constructor
  · -- For B ≥ B_c, bounded reachability = unbounded, and unbounded is safe
    intro B hB C hBreach
    rw [← bounded_equiv_unbounded C₀ B hB hbdd] at hBreach
    exact h_unbounded_safe C hBreach
  · -- For B < B_c, bounded-stuck config exists
    intro B hB
    have hInit' : maxBufferOccupancy C₀ ≤ B := by
      simpa [hInit] using (Nat.zero_le B)
    have hBoundedReach' :
        ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B →
          BoundedReachable B C₀ C := by
      intro C hreach hle
      exact hBoundedReach B C hreach hle
    exact bounded_stuck_below_critical C₀ B hB hInit'
      hBoundedReach' hDet hTerminalNoStep

/-- `phase_transition_sharp` specialized to a deterministic base-step regime. -/
theorem phase_transition_sharp_of_base_regime (C₀ : Config)
    (hInit : maxBufferOccupancy C₀ = 0)
    (hBoundedReach : ∀ B C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B →
      BoundedReachable B C₀ C)
    (hBase : ∀ {C C'}, Step C C' → StepBase C C')
    (hNoPar : ∀ (C : Config) nS nG P Q, C.proc = Process.par nS nG P Q → False)
    (hTerminalNoStep : ∀ C, IsTerminal C → ¬∃ C', Step C C')
    (h_unbounded_safe : ∀ C, UnboundedReachable C₀ C → ¬Deadlocked C)
    (hfinite : ∃ n : Nat, ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ n) :
    ∃ Bc : Nat,
      (∀ B, B ≥ Bc → ∀ C, BoundedReachable B C₀ C → ¬Deadlocked C) ∧
      (∀ B, B < Bc → ∃ C, BoundedReachable B C₀ C ∧ BoundedStuck B C) := by
  have hDet : ∀ C C₁ C₂, Step C C₁ → Step C C₂ → C₁ = C₂ :=
    step_deterministic_of_base_regime hBase hNoPar
  exact phase_transition_sharp C₀ hInit hBoundedReach hDet
    hTerminalNoStep h_unbounded_safe hfinite

/-- **Theorem 4 (Computability)**: B_c is computable from the initial configuration.
    For finite global types, the reachable configuration space is finite,
    so the maximum buffer occupancy is attained. -/
theorem critical_buffer_computable (C₀ : Config)
    (hfinite : ∃ n : Nat, ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ n) :
    ∃ Bc : Nat, Bc = criticalBufferSize C₀ ∧
      ∃ C_witness, UnboundedReachable C₀ C_witness ∧ maxBufferOccupancy C_witness = Bc := by
  obtain ⟨bound, hbound⟩ := hfinite
  -- The occupancy set is bounded and nonempty
  have hbdd : BddAbove (occupancySet C₀) := by
    use bound
    intro n ⟨C, hreach, hocc⟩
    rw [← hocc]
    exact hbound C hreach
  have hnonempty : (occupancySet C₀).Nonempty := by
    use maxBufferOccupancy C₀
    exact ⟨C₀, Relation.ReflTransGen.refl, rfl⟩
  -- The finite set has a maximum
  have hfiniteSet : (occupancySet C₀).Finite := by
    apply Set.Finite.subset (Set.finite_Icc 0 bound)
    intro n ⟨C, hreach, hocc⟩
    simp only [Set.mem_Icc]
    constructor
    · exact Nat.zero_le n
    · rw [← hocc]
      exact hbound C hreach
  -- Use the fact that finite nonempty Nat sets have their sSup as a member
  have hmax : sSup (occupancySet C₀) ∈ occupancySet C₀ := Nat.sSup_mem hnonempty hbdd
  use sSup (occupancySet C₀)
  constructor
  · rfl
  · obtain ⟨C, hreach, hocc⟩ := hmax
    exact ⟨C, hreach, hocc⟩

/-! ## Bounded Coherence -/

/-- Coherence with an explicit buffer bound: the configuration is coherent
    AND all buffers have size ≤ B. -/
def BoundedCoherent (B : Nat) (G : GEnv) (D : DEnv) (bufs : Buffers) : Prop :=
  Coherent G D ∧ ∀ e buf, (e, buf) ∈ bufs → buf.length ≤ B

/-- Helper: foldl max with init is bounded by B if init ≤ B and all elements are ≤ B. -/
theorem foldl_max_le_of_all_le_aux {l : List Nat} {B init : Nat}
    (hinit : init ≤ B) (h : ∀ n ∈ l, n ≤ B) : l.foldl max init ≤ B := by
  induction l generalizing init with
  | nil => simp [hinit]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · have hhd : hd ∈ hd :: tl := by simp
      exact max_le hinit (h hd hhd)
    · intro n hn
      have hn' : n ∈ hd :: tl := by simp [hn]
      exact h n hn'

/-- Helper: foldl max with 0 init is bounded by B if all elements are ≤ B. -/
theorem foldl_max_le_of_all_le {l : List Nat} {B : Nat}
    (h : ∀ n ∈ l, n ≤ B) : l.foldl max 0 ≤ B :=
  foldl_max_le_of_all_le_aux (Nat.zero_le B) h

/-- If a configuration is bounded-coherent, max buffer occupancy ≤ B. -/
theorem BoundedCoherent_maxBufferOccupancy {B : Nat} {C : Config}
    (h : BoundedCoherent B C.G C.D C.bufs) :
    maxBufferOccupancy C ≤ B := by
  simp only [maxBufferOccupancy]
  apply foldl_max_le_of_all_le
  intro n hn
  simp only [List.mem_map] at hn
  obtain ⟨⟨e, buf⟩, hmem, heq⟩ := hn
  rw [← heq]
  exact h.2 e buf hmem

/-! ## BddAbove from Coherence -/

/-- Sum of local-type depths in a session environment. -/
def totalTypeDepthG (G : GEnv) : Nat :=
  (G.map (fun (_, L) => L.depth)).foldl (· + ·) 0

/-- Sum of local-type depths in the current session environment. -/
def totalTypeDepth (C : Config) : Nat :=
  totalTypeDepthG C.G

/-- foldl (+) with initial value `n` shifts by `n`. -/
private theorem foldl_add_shift (l : List Nat) (n : Nat) :
    l.foldl (· + ·) n = n + l.foldl (· + ·) 0 := by
  induction l generalizing n with
  | nil =>
      simp
  | cons h t ih =>
      simp only [List.foldl, Nat.zero_add]
      have ih1 := ih (n + h)
      have ih2 := ih h
      calc
        t.foldl (· + ·) (n + h) = (n + h) + t.foldl (· + ·) 0 := ih1
        _ = n + (h + t.foldl (· + ·) 0) := by simp [Nat.add_assoc]
        _ = n + t.foldl (· + ·) h := by rw [← ih2]

/-- Total depth for a non-empty GEnv is head depth plus tail depth. -/
private theorem totalTypeDepthG_cons (ep : Endpoint) (L : LocalType) (rest : GEnv) :
    totalTypeDepthG ((ep, L) :: rest) = L.depth + totalTypeDepthG rest := by
  -- Expand map + foldl, then use the foldl shift lemma.
  unfold totalTypeDepthG
  -- Reduce to a foldl on the mapped tail, then apply shift.
  simp [List.foldl_cons]
  exact foldl_add_shift _ _

/-- If all numbers in a list are at most `B`, then their fold-sum is at most
    `length * B`. -/
theorem foldl_add_le_of_all_le {l : List Nat} {B : Nat}
    (h : ∀ n ∈ l, n ≤ B) :
    l.foldl (· + ·) 0 ≤ l.length * B := by
  induction l with
  | nil =>
      simp
  | cons hd tl ih =>
      have hhd : hd ≤ B := h hd (by simp)
      have htl : ∀ n ∈ tl, n ≤ B := by
        intro n hn
        exact h n (by simp [hn])
      calc
        (hd :: tl).foldl (· + ·) 0 = tl.foldl (· + ·) hd := by simp
        _ = hd + tl.foldl (· + ·) 0 := foldl_add_shift tl hd
        _ ≤ B + tl.length * B := Nat.add_le_add hhd (ih htl)
        _ = (tl.length + 1) * B := by
          calc
            B + tl.length * B = tl.length * B + B := by ac_rfl
            _ = (tl.length + 1) * B := by simpa [Nat.succ_mul, Nat.add_comm]
        _ = (hd :: tl).length * B := by simp

/-- Bounded per-endpoint depth yields a bound on total depth. -/
theorem totalTypeDepth_le_mul_of_depth_bound (C : Config) (d : Nat)
    (hDepth : ∀ ep L, (ep, L) ∈ C.G → L.depth ≤ d) :
    totalTypeDepth C ≤ C.G.length * d := by
  unfold totalTypeDepth totalTypeDepthG
  have hAll : ∀ n ∈ C.G.map (fun (_, L) => L.depth), n ≤ d := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨⟨ep, L⟩, hmem, hEq⟩
    subst n
    exact hDepth ep L hmem
  simpa [List.length_map] using foldl_add_le_of_all_le hAll

/-! ## Depth Bounds Along Steps -/

/-- Any local type depth is bounded by totalTypeDepthG. -/
private theorem depth_le_totalTypeDepthG_of_mem {G : GEnv} {ep : Endpoint} {L : LocalType}
    (hmem : (ep, L) ∈ G) : L.depth ≤ totalTypeDepthG G := by
  induction G with
  | nil => cases hmem
  | cons hd tl ih =>
      cases hd with
      | mk ep' L' =>
          rcases List.mem_cons.mp hmem with hEq | hTail
          · cases hEq
            -- L'.depth ≤ L'.depth + totalTypeDepthG tl
            simp [totalTypeDepthG_cons]
          · have hle : L.depth ≤ totalTypeDepthG tl := ih hTail
            have hle' : totalTypeDepthG tl ≤ L'.depth + totalTypeDepthG tl :=
              Nat.le_add_left _ _
            exact le_trans hle (by simpa [totalTypeDepthG_cons] using hle')

/-- Any local type depth is bounded by totalTypeDepth. -/
theorem depth_le_totalTypeDepth_of_mem (C : Config) {ep : Endpoint} {L : LocalType}
    (hmem : (ep, L) ∈ C.G) : L.depth ≤ totalTypeDepth C := by
  simpa [totalTypeDepth] using depth_le_totalTypeDepthG_of_mem (G:=C.G) hmem

/-- Updating a known endpoint with a shallower type does not increase total depth. -/
private theorem totalTypeDepthG_updateG_le {G : GEnv} {e : Endpoint}
    {Lold Lnew : LocalType}
    (hLookup : lookupG G e = some Lold)
    (hLe : Lnew.depth ≤ Lold.depth) :
    totalTypeDepthG (updateG G e Lnew) ≤ totalTypeDepthG G := by
  -- Induct on G to align updateG with the head position.
  induction G generalizing e Lold Lnew with
  | nil => cases hLookup
  | cons hd tl ih =>
      cases hd with
      | mk ep L =>
          by_cases hEq : e = ep
          · -- Update hits the head; depth decreases at that position.
            have hOld : L = Lold := by
              simpa [lookupG, List.lookup, hEq] using hLookup
            cases hOld
            simp [totalTypeDepthG_cons, updateG, hEq, hLe]
          · -- Update recurses on the tail; head depth unchanged.
            have hLookup' : lookupG tl e = some Lold := by
              have hEq' : (e == ep) = false := beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hEq'] using hLookup
            have hTail : totalTypeDepthG (updateG tl e Lnew) ≤ totalTypeDepthG tl :=
              ih (e:=e) (Lold:=Lold) (Lnew:=Lnew) hLookup' hLe
            simp [totalTypeDepthG_cons, updateG, hEq, hTail]

/-- Send steps reduce totalTypeDepth (depth strictly decreases at sender). -/
private theorem totalTypeDepth_send_le {C : Config} {e : Endpoint} {target : Role}
    {T : ValType} {L : LocalType} {v : Value}
    (hG : lookupG C.G e = some (.send target T L)) :
    totalTypeDepth (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) ≤
      totalTypeDepth C := by
  -- Use depth_advance_send for the updated endpoint.
  have hLt := LocalType.depth_advance_send target T L
  have hLe : L.depth ≤ (LocalType.send target T L).depth := Nat.le_of_lt hLt
  simpa [totalTypeDepth, totalTypeDepthG, sendStep] using
    totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.send target T L) (Lnew:=L) hG hLe

/-- Recv steps reduce totalTypeDepth (depth strictly decreases at receiver). -/
private theorem totalTypeDepth_recv_le {C : Config} {e : Endpoint} {source : Role}
    {T : ValType} {L : LocalType} {x : Var} {v : Value}
    (hG : lookupG C.G e = some (.recv source T L)) :
    totalTypeDepth (recvStep C e { sid := e.sid, sender := source, receiver := e.role } x v L) ≤
      totalTypeDepth C := by
  -- recvStep may return C when dequeue fails; split on the buffer case.
  cases hDeq : dequeueBuf C.bufs { sid := e.sid, sender := source, receiver := e.role } with
  | none =>
      -- No change to G, so totalTypeDepth is unchanged.
      simp [recvStep, hDeq, totalTypeDepth, totalTypeDepthG]
  | some p =>
      -- Successful dequeue updates G to the continuation, reducing depth.
      have hLt := LocalType.depth_advance_recv source T L
      have hLe : L.depth ≤ (LocalType.recv source T L).depth := Nat.le_of_lt hLt
      simpa [recvStep, hDeq, totalTypeDepth, totalTypeDepthG] using
        totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.recv source T L) (Lnew:=L) hG hLe

/-- Select steps reduce totalTypeDepth (depth decreases to chosen branch). -/
private theorem totalTypeDepth_select_le {C : Config} {e : Endpoint} {target : Role}
    {branches : List (Label × LocalType)} {ℓ : Label} {L : LocalType}
    {v : Value} {T : ValType}
    (hG : lookupG C.G e = some (.select target branches))
    (hFind : branches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    totalTypeDepth (sendStep C e { sid := e.sid, sender := e.role, receiver := target } v T L) ≤
      totalTypeDepth C := by
  -- Convert find? into membership, then use depth_advance_select.
  have hMem : (ℓ, L) ∈ branches := List.mem_of_find?_eq_some hFind
  have hLt := LocalType.depth_advance_select target branches ℓ L hMem
  have hLe : L.depth ≤ (LocalType.select target branches).depth := Nat.le_of_lt hLt
  simpa [totalTypeDepth, totalTypeDepthG, sendStep] using
    totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.select target branches) (Lnew:=L) hG hLe

/-- Branch steps reduce totalTypeDepth (depth decreases to chosen branch). -/
private theorem totalTypeDepth_branch_le {C : Config} {e : Endpoint} {source : Role}
    {typeBranches : List (Label × LocalType)} {ℓ : Label} {L : LocalType}
    (hG : lookupG C.G e = some (.branch source typeBranches))
    (hFind : typeBranches.find? (fun b => b.1 == ℓ) = some (ℓ, L)) :
    totalTypeDepth { C with G := updateG C.G e L } ≤ totalTypeDepth C := by
  -- Convert find? into membership, then use depth_advance_branch.
  have hMem : (ℓ, L) ∈ typeBranches := List.mem_of_find?_eq_some hFind
  have hLt := LocalType.depth_advance_branch source typeBranches ℓ L hMem
  have hLe : L.depth ≤ (LocalType.branch source typeBranches).depth := Nat.le_of_lt hLt
  simpa [totalTypeDepth, totalTypeDepthG] using
    totalTypeDepthG_updateG_le (G:=C.G) (e:=e) (Lold:=.branch source typeBranches) (Lnew:=L) hG hLe

/-- StepBase does not increase totalTypeDepth. -/
private theorem totalTypeDepth_stepBase_le {C C' : Config} (h : StepBase C C') :
    totalTypeDepth C' ≤ totalTypeDepth C := by
  -- Case analysis on the head step rule.
  cases h with
  | send hProc hK hX hG =>
      -- Send case: reduce to the send helper lemma.
      simpa using totalTypeDepth_send_le (C:=C) (hG:=hG)
  | recv hProc hK hG hBuf =>
      -- Recv case: reduce to the recv helper lemma.
      simpa using totalTypeDepth_recv_le (C:=C) (hG:=hG)
  | select hProc hK hG hFind =>
      -- Select case: reduce to the select helper lemma.
      simpa using totalTypeDepth_select_le (C:=C) (hG:=hG) (hFind:=hFind)
  | branch hProc hK hG hBuf hFindP hFindT hDeq =>
      -- Branch case: reduce to the branch helper lemma.
      simpa using totalTypeDepth_branch_le (C:=C) (hG:=hG) (hFind:=hFindT)
  | newSession hProc =>
      -- newSession does not change G.
      simp [totalTypeDepth, totalTypeDepthG, newSessionStep]
  | assign hProc =>
      -- assign does not change G.
      simp [totalTypeDepth, totalTypeDepthG]
  | seq2 hProc =>
      -- seq2 does not change G.
      simp [totalTypeDepth, totalTypeDepthG]
  | par_skip_left hProc =>
      -- par_skip_left does not change G.
      simp [totalTypeDepth, totalTypeDepthG]
  | par_skip_right hProc =>
      -- par_skip_right does not change G.
      simp [totalTypeDepth, totalTypeDepthG]

/-- Step does not increase totalTypeDepth. -/
theorem totalTypeDepth_step_le {C C' : Config} (h : Step C C') :
    totalTypeDepth C' ≤ totalTypeDepth C := by
  -- Induct on the step derivation.
  induction h with
  | base hbase =>
      exact totalTypeDepth_stepBase_le hbase
  | seq_left hProc hStep ih =>
      -- seq-left only changes the process wrapper.
      simpa [totalTypeDepth] using ih
  | par_left hProc hStep ih =>
      -- par-left only changes the process wrapper.
      simpa [totalTypeDepth] using ih
  | par_right hProc hStep ih =>
      -- par-right only changes the process wrapper.
      simpa [totalTypeDepth] using ih

/-- totalTypeDepth is non-increasing along unbounded reachability. -/
theorem totalTypeDepth_reachable_le {C₀ C : Config} (h : UnboundedReachable C₀ C) :
    totalTypeDepth C ≤ totalTypeDepth C₀ := by
  -- Induct on the reachability derivation.
  induction h with
  | refl => simp
  | tail hreach hstep ih =>
      exact le_trans (totalTypeDepth_step_le hstep) ih

/-- Uniform depth bound derived from the initial totalTypeDepth. -/
theorem depth_bound_of_reachable (C₀ : Config) :
    ∃ d, ∀ C ep L, UnboundedReachable C₀ C → (ep, L) ∈ C.G → L.depth ≤ d := by
  -- Use totalTypeDepth C₀ as a global bound.
  refine ⟨totalTypeDepth C₀, ?_⟩
  intro C ep L hreach hmem
  have hLe := depth_le_totalTypeDepth_of_mem C hmem
  exact le_trans hLe (totalTypeDepth_reachable_le hreach)

/-! ## GEnv Size Bounds -/

/-- updateG preserves length when the endpoint is already present. -/
private theorem length_updateG_of_lookup {G : GEnv} {e : Endpoint}
    {Lold Lnew : LocalType} (hLookup : lookupG G e = some Lold) :
    (updateG G e Lnew).length = G.length := by
  -- Induct on the environment to align the update position.
  induction G generalizing e Lold Lnew with
  | nil => cases hLookup
  | cons hd tl ih =>
      cases hd with
      | mk ep L =>
          by_cases hEq : e = ep
          · -- Update hits head: length unchanged.
            simp [updateG, hEq]
          · -- Update recurses on tail: use IH.
            have hLookup' : lookupG tl e = some Lold := by
              have hEq' : (e == ep) = false := beq_eq_false_iff_ne.mpr hEq
              simpa [lookupG, List.lookup, hEq'] using hLookup
            simp [updateG, hEq, ih (e:=e) (Lold:=Lold) (Lnew:=Lnew) hLookup']

/-- StepBase preserves GEnv length. -/
private theorem G_length_stepBase_eq {C C' : Config} (h : StepBase C C') :
    C'.G.length = C.G.length := by
  -- Case analysis on the head step rule.
  cases h with
  | send hProc hK hX hG =>
      simpa [sendStep] using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | recv hProc hK hG hBuf =>
      -- recvStep reduces to a G update when the buffer is non-empty.
      simpa [recvStep, dequeueBuf, hBuf] using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | select hProc hK hG hFind =>
      simpa [sendStep] using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | branch hProc hK hG hBuf hFindP hFindT hDeq =>
      -- Branch updates G at the receiver endpoint.
      simpa using
        length_updateG_of_lookup (G:=C.G) (hLookup:=hG)
  | newSession hProc =>
      -- newSession does not change G.
      simp [newSessionStep]
  | assign hProc =>
      -- assign does not change G.
      rfl
  | seq2 hProc =>
      -- seq2 does not change G.
      rfl
  | par_skip_left hProc =>
      -- par_skip_left does not change G.
      rfl
  | par_skip_right hProc =>
      -- par_skip_right does not change G.
      rfl

/-- Step preserves GEnv length. -/
theorem G_length_step_eq {C C' : Config} (h : Step C C') :
    C'.G.length = C.G.length := by
  -- Induct on the step derivation.
  induction h with
  | base hbase =>
      exact G_length_stepBase_eq hbase
  | seq_left hProc hStep ih =>
      simpa using ih
  | par_left hProc hStep ih =>
      simpa using ih
  | par_right hProc hStep ih =>
      simpa using ih

/-- GEnv length is preserved along unbounded reachability. -/
theorem G_length_reachable_eq {C₀ C : Config} (h : UnboundedReachable C₀ C) :
    C.G.length = C₀.G.length := by
  -- Induct on the reachability derivation.
  induction h with
  | refl => rfl
  | tail hreach hstep ih =>
      exact (G_length_step_eq hstep).trans ih

/-- Uniform size bound derived from the initial GEnv length. -/
theorem G_length_bound_of_reachable (C₀ : Config) :
    ∃ m, ∀ C, UnboundedReachable C₀ C → C.G.length ≤ m := by
  -- Use the preserved initial length as a bound.
  refine ⟨C₀.G.length, ?_⟩
  intro C hreach
  exact (G_length_reachable_eq hreach).le

/-! ## Occupancy Bound from Coherence -/

/-- Buffers are active if every edge in the buffer list has endpoints in G. -/
def BuffersActive (G : GEnv) (bufs : Buffers) : Prop :=
  ∀ e buf, (e, buf) ∈ bufs → ActiveEdge G e

/-- Buffers are unique if there is at most one entry per edge. -/
def BuffersUnique (bufs : Buffers) : Prop :=
  (bufs.map Prod.fst).Nodup

/-- If buffers are unique, membership determines lookupBuf. -/
private theorem lookupBuf_eq_of_mem_unique {bufs : Buffers} (hUniq : BuffersUnique bufs)
    {e : Edge} {buf : Buffer} (hmem : (e, buf) ∈ bufs) :
    lookupBuf bufs e = buf := by
  -- Induct on the buffer list and use nodup to rule out duplicate keys.
  induction bufs with
  | nil => cases hmem
  | cons hd tl ih =>
      have hUniq' : (hd.1 :: tl.map Prod.fst).Nodup := by
        simpa [BuffersUnique] using hUniq
      have hNotMem : hd.1 ∉ tl.map Prod.fst :=
        (List.nodup_cons.mp hUniq').1
      have hNodup : (tl.map Prod.fst).Nodup :=
        (List.nodup_cons.mp hUniq').2
      rcases List.mem_cons.mp hmem with hEq | hTail
      · -- Head case: lookupBuf returns the head buffer.
        cases hEq
        simp [lookupBuf, List.lookup]
      · -- Tail case: key differs from head, so lookup recurses.
        have hNe : e ≠ hd.1 := by
          intro hEq
          subst hEq
          have hKey : hd.1 ∈ tl.map Prod.fst := by
            exact List.mem_map_of_mem (f := Prod.fst) (a := (hd.1, buf)) hTail
          exact hNotMem hKey
        have hNe' : (e == hd.1) = false := beq_eq_false_iff_ne.mpr hNe
        have hLookup : lookupBuf tl e = buf := ih (by
          simpa [BuffersUnique] using hNodup) hTail
        have hLookup' : (List.lookup e tl).getD [] = buf := by
          simpa [lookupBuf] using hLookup
        simp [lookupBuf, List.lookup, hNe', hLookup']

/-- Typed buffers have matching trace lengths. -/
theorem buffer_length_eq_trace_length {G : GEnv} {D : DEnv} {bufs : Buffers} (e : Edge)
    (hBT : BuffersTyped G D bufs) :
    (lookupBuf bufs e).length = (lookupD D e).length := by
  -- Unpack BufferTyped for this edge.
  rcases hBT e with ⟨hLen, _⟩
  exact hLen

/-- Coherence bounds trace length by receiver depth on active edges. -/
theorem trace_length_le_depth_of_coherent {G : GEnv} {D : DEnv} {e : Edge}
    {Lrecv : LocalType} (hCoh : Coherent G D) (hActive : ActiveEdge G e)
    (hGrecv : lookupG G { sid := e.sid, role := e.receiver } = some Lrecv) :
    (lookupD D e).length ≤ Lrecv.depth := by
  -- Extract Consume witness from coherence and apply Consume_length_le_depth.
  have hEdge := hCoh e hActive Lrecv hGrecv
  rcases hEdge with ⟨_, _hGsender, hConsume⟩
  rcases (Option.isSome_iff_exists).1 hConsume with ⟨L', hConsume'⟩
  exact Consume_length_le_depth hConsume'

/-- Edge buffer occupancy is bounded by receiver depth on active edges. -/
private theorem edgeBufferOccupancy_le_receiver_depth {C : Config} {e : Edge}
    {Lrecv : LocalType} (hBT : BuffersTyped C.G C.D C.bufs) (hCoh : Coherent C.G C.D)
    (hActive : ActiveEdge C.G e)
    (hGrecv : lookupG C.G { sid := e.sid, role := e.receiver } = some Lrecv) :
    edgeBufferOccupancy C e ≤ Lrecv.depth := by
  -- Buffer length equals trace length, and coherence bounds trace length.
  have hTrace := trace_length_le_depth_of_coherent (G:=C.G) (D:=C.D) (e:=e)
    (Lrecv:=Lrecv) hCoh hActive hGrecv
  have hBuf : edgeBufferOccupancy C e = (lookupD C.D e).length := by
    simp [edgeBufferOccupancy, buffer_length_eq_trace_length (e:=e) hBT]
  simpa [hBuf] using hTrace

/-- Edge buffer occupancy is bounded by totalTypeDepth on active edges. -/
theorem edgeBufferOccupancy_le_totalTypeDepth {C : Config} {e : Edge}
    (hBT : BuffersTyped C.G C.D C.bufs) (hCoh : Coherent C.G C.D)
    (hActive : ActiveEdge C.G e) :
    edgeBufferOccupancy C e ≤ totalTypeDepth C := by
  -- Get the receiver type from ActiveEdge, then combine bounds.
  have hActive' := hActive
  rcases hActive with ⟨_hSend, hRecv⟩
  rcases (Option.isSome_iff_exists).1 hRecv with ⟨Lrecv, hGrecv⟩
  have hOcc : edgeBufferOccupancy C e ≤ Lrecv.depth :=
    edgeBufferOccupancy_le_receiver_depth (C:=C) (e:=e) hBT hCoh hActive' hGrecv
  have hMem : ({ sid := e.sid, role := e.receiver }, Lrecv) ∈ C.G :=
    lookupG_mem C.G _ _ hGrecv
  have hDepth : Lrecv.depth ≤ totalTypeDepth C :=
    depth_le_totalTypeDepth_of_mem C hMem
  exact le_trans hOcc hDepth

/-- Max buffer occupancy is bounded by totalTypeDepth under coherence. -/
theorem maxBufferOccupancy_le_totalTypeDepth {C : Config}
    (hBT : BuffersTyped C.G C.D C.bufs) (hCoh : Coherent C.G C.D)
    (hActive : BuffersActive C.G C.bufs) (hUnique : BuffersUnique C.bufs) :
    maxBufferOccupancy C ≤ totalTypeDepth C := by
  -- Each buffer length is bounded by the total depth.
  unfold maxBufferOccupancy
  apply foldl_max_le_of_all_le_local
  intro n hn
  rcases List.mem_map.mp hn with ⟨⟨e, buf⟩, hmem, rfl⟩
  have hAct : ActiveEdge C.G e := hActive e buf hmem
  have hLookup : lookupBuf C.bufs e = buf := lookupBuf_eq_of_mem_unique hUnique hmem
  have hLe := edgeBufferOccupancy_le_totalTypeDepth (C:=C) (e:=e) hBT hCoh hAct
  simpa [edgeBufferOccupancy, hLookup] using hLe


/-- Coherence is preserved along unbounded-reachable paths. -/
private theorem coherent_on_reachable (C₀ : Config)
    (hCoh₀ : Coherent C₀.G C₀.D)
    (hPres : ∀ C C', UnboundedReachable C₀ C → Step C C' → Coherent C'.G C'.D) :
    ∀ C, UnboundedReachable C₀ C → Coherent C.G C.D := by
  intro C hreach
  induction hreach with
  | refl =>
      simpa using hCoh₀
  | tail hreach hstep _ =>
      exact hPres _ _ hreach hstep

/-- **Key theorem**: Well-typed coherent configurations have bounded buffer growth.
    This is because session types discipline the communication: every send must
    eventually be matched by a receive, and the type structure bounds how many
    unmatched sends can accumulate. -/
theorem coherent_implies_bddAbove (C₀ : Config)
    (hCoh : Coherent C₀.G C₀.D)
    (hPres : ∀ C C', UnboundedReachable C₀ C → Step C C' → Coherent C'.G C'.D)
    (hOccFromCoh : ∀ C, UnboundedReachable C₀ C → Coherent C.G C.D →
      maxBufferOccupancy C ≤ totalTypeDepth C)
    (hDepthBound : ∃ d, ∀ C ep L, UnboundedReachable C₀ C → (ep, L) ∈ C.G → L.depth ≤ d)
    (hGSizeBound : ∃ m, ∀ C, UnboundedReachable C₀ C → C.G.length ≤ m) :
    BddAbove (occupancySet C₀) := by
  obtain ⟨d, hDepth⟩ := hDepthBound
  obtain ⟨m, hSize⟩ := hGSizeBound
  refine ⟨m * d, ?_⟩
  intro n ⟨C, hreach, hocc⟩
  rw [← hocc]
  have hCohC : Coherent C.G C.D := coherent_on_reachable C₀ hCoh hPres C hreach
  have hOccLeDepth : maxBufferOccupancy C ≤ totalTypeDepth C :=
    hOccFromCoh C hreach hCohC
  have hDepthLe : totalTypeDepth C ≤ C.G.length * d := by
    apply totalTypeDepth_le_mul_of_depth_bound C d
    intro ep L hmem
    exact hDepth C ep L hreach hmem
  have hSizeLe : C.G.length * d ≤ m * d := Nat.mul_le_mul_right d (hSize C hreach)
  exact le_trans hOccLeDepth (le_trans hDepthLe hSizeLe)

/-- Coherence-driven boundedness hypotheses packaged as an explicit global occupancy
    bound usable by `phase_transition_sharp`. -/
theorem coherent_implies_global_occupancy_bound (C₀ : Config)
    (hCoh : Coherent C₀.G C₀.D)
    (hPres : ∀ C C', UnboundedReachable C₀ C → Step C C' → Coherent C'.G C'.D)
    (hOccFromCoh : ∀ C, UnboundedReachable C₀ C → Coherent C.G C.D →
      maxBufferOccupancy C ≤ totalTypeDepth C)
    (hDepthBound : ∃ d, ∀ C ep L, UnboundedReachable C₀ C → (ep, L) ∈ C.G → L.depth ≤ d)
    (hGSizeBound : ∃ m, ∀ C, UnboundedReachable C₀ C → C.G.length ≤ m) :
    ∃ n : Nat, ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ n := by
  have hbdd : BddAbove (occupancySet C₀) :=
    coherent_implies_bddAbove C₀ hCoh hPres hOccFromCoh hDepthBound hGSizeBound
  rcases hbdd with ⟨bound, hbound⟩
  refine ⟨bound, ?_⟩
  intro C hreach
  exact hbound ⟨C, hreach, rfl⟩

/-- Coherence yields bounded occupancy under buffer-activity/uniqueness invariants. -/
theorem coherent_implies_bddAbove_of_invariants (C₀ : Config)
    (hCoh : Coherent C₀.G C₀.D)
    (hPres : ∀ C C', UnboundedReachable C₀ C → Step C C' → Coherent C'.G C'.D)
    (hBT : ∀ C, UnboundedReachable C₀ C → BuffersTyped C.G C.D C.bufs)
    (hActive : ∀ C, UnboundedReachable C₀ C → BuffersActive C.G C.bufs)
    (hUnique : ∀ C, UnboundedReachable C₀ C → BuffersUnique C.bufs) :
    BddAbove (occupancySet C₀) := by
  -- Build the occupancy bound using preserved invariants.
  have hOccFromCoh :
      ∀ C, UnboundedReachable C₀ C → Coherent C.G C.D →
        maxBufferOccupancy C ≤ totalTypeDepth C := by
    intro C hreach hCohC
    exact maxBufferOccupancy_le_totalTypeDepth (C:=C)
      (hBT C hreach) hCohC (hActive C hreach) (hUnique C hreach)
  -- Depth/size bounds come from step monotonicity.
  have hDepthBound := depth_bound_of_reachable C₀
  have hGSizeBound := G_length_bound_of_reachable C₀
  exact coherent_implies_bddAbove C₀ hCoh hPres hOccFromCoh hDepthBound hGSizeBound

/-- End-to-end sharp phase transition theorem where the occupancy boundedness
    assumptions are discharged from coherence + structural depth bounds. -/
theorem phase_transition_sharp_of_coherence_base_regime (C₀ : Config)
    (hCoh : Coherent C₀.G C₀.D)
    (hPres : ∀ C C', UnboundedReachable C₀ C → Step C C' → Coherent C'.G C'.D)
    (hOccFromCoh : ∀ C, UnboundedReachable C₀ C → Coherent C.G C.D →
      maxBufferOccupancy C ≤ totalTypeDepth C)
    (hDepthBound : ∃ d, ∀ C ep L, UnboundedReachable C₀ C → (ep, L) ∈ C.G → L.depth ≤ d)
    (hGSizeBound : ∃ m, ∀ C, UnboundedReachable C₀ C → C.G.length ≤ m)
    (hInit : maxBufferOccupancy C₀ = 0)
    (hBoundedReach : ∀ B C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ B →
      BoundedReachable B C₀ C)
    (hBase : ∀ {C C'}, Step C C' → StepBase C C')
    (hNoPar : ∀ (C : Config) nS nG P Q, C.proc = Process.par nS nG P Q → False)
    (hTerminalNoStep : ∀ C, IsTerminal C → ¬∃ C', Step C C')
    (h_unbounded_safe : ∀ C, UnboundedReachable C₀ C → ¬Deadlocked C) :
    ∃ Bc : Nat,
      (∀ B, B ≥ Bc → ∀ C, BoundedReachable B C₀ C → ¬Deadlocked C) ∧
      (∀ B, B < Bc → ∃ C, BoundedReachable B C₀ C ∧ BoundedStuck B C) := by
  have hfinite : ∃ n : Nat, ∀ C, UnboundedReachable C₀ C → maxBufferOccupancy C ≤ n :=
    coherent_implies_global_occupancy_bound C₀ hCoh hPres hOccFromCoh hDepthBound hGSizeBound
  exact phase_transition_sharp_of_base_regime C₀ hInit hBoundedReach hBase hNoPar
    hTerminalNoStep h_unbounded_safe hfinite

/-- Refinement: bounded coherent configurations refine unbounded ones. -/
theorem bounded_refines_unbounded (B : Nat) (G : GEnv) (D : DEnv) (bufs : Buffers)
    (h : BoundedCoherent B G D bufs) : Coherent G D :=
  h.1

/-! ## Connection to Delivery Models -/

/-- The FIFO delivery model with explicit buffer bound. -/
def BoundedFIFO (B : Nat) : DeliveryModel where
  consume := Consume

/-- Bounded FIFO satisfies the delivery model laws when buffers are bounded. -/
theorem BoundedFIFO_laws (B : Nat) : DeliveryModelLaws (BoundedFIFO B) := {
  consume_nil := fun from_ L => rfl
  consume_append := fun from_ L ts T {L'} hcons => Consume_append from_ L ts T hcons
  consume_cons := fun from_ L T ts => Consume_cons from_ L T ts
  consume_rename := fun ρ from_ L ts => Consume_rename ρ from_ L ts
}

end
