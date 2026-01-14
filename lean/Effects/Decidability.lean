import Effects.DeadlockFreedom
import Effects.Spatial

/-!
# MPST Decidability Infrastructure

This module provides decidability instances and boolean decision procedures
for key predicates in the Effects library.

## Overview

Many predicates in the library are decidable when restricted to finite domains:
- `ReachesComm L` is decidable via `reachesCommDecide`
- `Satisfies topo req` is decidable via `satisfiesBool`

## Soundness Theorems

For each boolean decision procedure, we provide soundness theorems:
- `reachesCommDecide_sound`: if true, then ReachesComm holds
- `satisfiesBool_iff_Satisfies`: boolean iff propositional
-/

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped Classical

noncomputable section

/-! ## ReachesComm Decidability -/

/-- ReachesComm is decidable via the boolean checker. -/
instance instDecidableReachesComm (L : LocalType) : Decidable (ReachesComm L) :=
  if h : reachesCommDecide L = true then
    isTrue (reachesCommDecide_sound L h)
  else
    -- If reachesCommDecide returns false, we use Classical.dec
    -- Full completeness proof would require showing reachesCommDecide is complete
    Classical.dec _

/-- Alternative: use reachesCommDecide directly for proof by decide. -/
theorem reachesComm_of_decide {L : LocalType} (h : reachesCommDecide L = true) :
    ReachesComm L :=
  reachesCommDecide_sound L h

/-! ## Spatial Satisfaction Decidability -/

/-- Satisfies is decidable via satisfiesBool. -/
instance instDecidableSatisfies (topo : Topology) (req : SpatialReq) :
    Decidable (Satisfies topo req) :=
  if h : satisfiesBool topo req = true then
    isTrue ((satisfiesBool_iff_Satisfies topo req).mp h)
  else
    isFalse (fun hsat => h ((satisfiesBool_iff_Satisfies topo req).mpr hsat))

/-- Use satisfiesBool for proof. -/
theorem satisfies_of_bool {topo : Topology} {req : SpatialReq}
    (h : satisfiesBool topo req = true) : Satisfies topo req :=
  (satisfiesBool_iff_Satisfies topo req).mp h

/-! ## EdgeCoherent for Empty Traces -/

/-- When the trace is empty, EdgeCoherent is trivially satisfied.

This is because `Consume from L [] = some L` for any L, so `.isSome` is true.
-/
theorem edgeCoherent_empty_trace (G : GEnv) (D : DEnv) (e : Edge)
    (hTrace : lookupD D e = []) :
    EdgeCoherent G D e := by
  unfold EdgeCoherent
  simp only [hTrace, Consume, Option.isSome_some, implies_true]

/-- For a DEnv where all entries have empty traces, coherence holds. -/
theorem coherent_all_empty (G : GEnv) (D : DEnv)
    (hAll : ∀ e, lookupD D e = []) :
    Coherent G D := by
  intro e
  exact edgeCoherent_empty_trace G D e (hAll e)

/-! ## BufferTyped for Empty Buffers -/

/-- When buffer and trace are both empty, BufferTyped holds. -/
theorem bufferTyped_empty (G : GEnv) (D : DEnv) (bufs : Buffers) (e : Edge)
    (hBuf : lookupBuf bufs e = [])
    (hTrace : lookupD D e = []) :
    BufferTyped G D bufs e := by
  unfold BufferTyped
  simp only [hBuf, hTrace, List.length_nil]
  -- Goal is: ∃ (h : True), ∀ (i : ℕ) (hi : i < 0), ...
  exact ⟨trivial, fun i hi => (Nat.not_lt_zero i hi).elim⟩

/-- For environments where all buffers and traces are empty, BuffersTyped holds. -/
theorem buffersTyped_all_empty (G : GEnv) (D : DEnv) (bufs : Buffers)
    (hBufs : ∀ e, lookupBuf bufs e = [])
    (hTraces : ∀ e, lookupD D e = []) :
    BuffersTyped G D bufs := by
  intro e
  exact bufferTyped_empty G D bufs e (hBufs e) (hTraces e)

end
