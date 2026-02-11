import Protocol.BufferBoundedness.DepthBounds

/-! # Protocol.BufferBoundedness.OccupancyDelivery

Occupancy bounds from coherence and delivery-model connection.
-/

/-
The Problem. Final boundedness results must connect coherence-derived bounds to
explicit delivery-model abstractions.

Solution Structure. Proves occupancy bounds from coherence and packages the
bounded FIFO delivery model result.
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped Classical

section

/-! ## Occupancy Bound from Coherence -/

/-- Buffers are active if every edge in the buffer list has endpoints in G. -/
def BuffersActive (G : GEnv) (bufs : Buffers) : Prop :=
  ∀ e buf, (e, buf) ∈ bufs → ActiveEdge G e

/-- Buffers are unique if there is at most one entry per edge. -/
def BuffersUnique (bufs : Buffers) : Prop :=
  (bufs.map Prod.fst).Nodup

/-- If buffers are unique, membership determines lookupBuf. -/
theorem lookupBuf_eq_of_mem_unique {bufs : Buffers} (hUniq : BuffersUnique bufs)
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
theorem edgeBufferOccupancy_le_receiver_depth {C : Config} {e : Edge}
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
theorem coherent_on_reachable (C₀ : Config)
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
