import Protocol.BufferBoundedness.Basics

/-! # Protocol.BufferBoundedness.PhaseSharpness

Phase-transition and bounded-coherence lemmas.
-/

/-
The Problem. We need mid-layer phase-sharpness and bounded-coherence results
before proving global depth/occupancy bounds.

Solution Structure. Contains phase-transition and bounded-coherence lemmas used
by the later global-bound derivations.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

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
theorem not_terminal_of_step
    (hTerminalNoStep : ∀ C, IsTerminal C → ¬∃ C', Step C C')
    {C C' : Config} (hstep : Step C C') : ¬IsTerminal C := by
  -- Terminal configurations have no outgoing steps.
  intro hTerm
  exact hTerminalNoStep C hTerm ⟨C', hstep⟩

/-- Find the first step that crosses the buffer bound along an unbounded path. -/
theorem exists_first_overflow
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
theorem bounded_step_eq_succ
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
theorem no_bounded_step_of_overflow
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
theorem foldl_add_shift (l : List Nat) (n : Nat) :
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
theorem totalTypeDepthG_cons (ep : Endpoint) (L : LocalType) (rest : GEnv) :
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


end
