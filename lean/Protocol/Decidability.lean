import Protocol.DeadlockFreedom
import Protocol.Spatial


/-! # MPST Decidability Infrastructure

This module provides decidability instances and boolean decision procedures
for key predicates in the Protocol library.

## Overview

Many predicates in the library are decidable when restricted to finite domains:
- `ReachesComm L` is decidable via `reachesCommDecide`
- `Satisfies topo req` is decidable via `satisfiesBool`

## Soundness Theorems

For each boolean decision procedure, we provide soundness theorems:
- `reaches_comm_decide_sound`: if true, then ReachesComm holds
- `satisfies_bool_iff_satisfies`: boolean iff propositional
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

section

/-! ## ReachesComm Decision Support -/

/- We provide a sound boolean-to-proposition bridge.
   A full `Decidable (ReachesComm L)` instance is deferred until
   a complete false-branch theorem is established for `reachesCommDecide`. -/

/-- Alternative: use reachesCommDecide directly for proof by decide. -/
theorem reaches_comm_of_decide {L : LocalType} (h : reachesCommDecide L = true) :
    ReachesComm L :=
  reaches_comm_decide_sound L h

/-! ## Spatial Satisfaction Decidability -/

/-- Satisfies is decidable via satisfiesBool. -/
instance instDecidableSatisfies (topo : Topology) (req : SpatialReq) :
    Decidable (Satisfies topo req) :=
  if h : satisfiesBool topo req = true then
    isTrue ((satisfies_bool_iff_satisfies topo req).mp h)
  else
    isFalse (fun hsat => h ((satisfies_bool_iff_satisfies topo req).mpr hsat))

/-- Use satisfiesBool for proof. -/
theorem satisfies_of_bool {topo : Topology} {req : SpatialReq}
    (h : satisfiesBool topo req = true) : Satisfies topo req :=
  (satisfies_bool_iff_satisfies topo req).mp h

/-! ## EdgeCoherent for Empty Traces -/

/-- When the trace is empty, EdgeCoherent is trivially satisfied.

This is because `Consume from L [] = some L` for any L, so `.isSome` is true.
-/
theorem edge_coherent_empty_trace (G : GEnv) (D : DEnv) (e : Edge)
    (hTrace : lookupD D e = [])
    (hSender : ∀ Lrecv, lookupG G { sid := e.sid, role := e.receiver } = some Lrecv →
      ∃ Lsender, lookupG G { sid := e.sid, role := e.sender } = some Lsender) :
    EdgeCoherent G D e := by
  intro Lrecv hGrecv
  rcases hSender Lrecv hGrecv with ⟨Lsender, hGsender⟩
  refine ⟨Lsender, hGsender, ?_⟩
  simp [hTrace, Consume]

/-- For a DEnv where all entries have empty traces, coherence holds. -/
theorem coherent_all_empty (G : GEnv) (D : DEnv)
    (hAll : ∀ e : Edge, lookupD D e = [])
    (hSenders : ∀ e : Edge, ∀ Lrecv : LocalType,
      lookupG G { sid := e.sid, role := e.receiver } = some Lrecv →
      ∃ Lsender, lookupG G { sid := e.sid, role := e.sender } = some Lsender) :
    Coherent G D := by
  intro e hActive
  exact edge_coherent_empty_trace G D e (hAll e) (hSenders e)

/-! ## BufferTyped for Empty Buffers -/

/-- When buffer and trace are both empty, BufferTyped holds. -/
theorem buffer_typed_empty (G : GEnv) (D : DEnv) (bufs : Buffers) (e : Edge)
    (hBuf : lookupBuf bufs e = [])
    (hTrace : lookupD D e = []) :
    BufferTyped G D bufs e := by
  unfold BufferTyped
  simp only [hBuf, hTrace, List.length_nil]
  -- Goal is: ∃ (h : True), ∀ (i : ℕ) (hi : i < 0), ...
  exact ⟨trivial, fun i hi => (Nat.not_lt_zero i hi).elim⟩

/-- For environments where all buffers and traces are empty, BuffersTyped holds. -/
theorem buffers_typed_all_empty (G : GEnv) (D : DEnv) (bufs : Buffers)
    (hBufs : ∀ e, lookupBuf bufs e = [])
    (hTraces : ∀ e, lookupD D e = []) :
    BuffersTyped G D bufs := by
  intro e
  exact buffer_typed_empty G D bufs e (hBufs e) (hTraces e)

end
