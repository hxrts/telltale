import Protocol.Classical.Instantiation.FosterAndQueueing
import Protocol.CrashToleranceDrain

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! # Foster-Lyapunov Instance from Message Delivery

A genuine instance of `FosterLivenessAssumptions`: the Lyapunov function is the
number of in-flight messages on active edges (`drainMeasure`), and the step
delivers one in-flight message when any exists (identity otherwise).
Non-increase and strict decrease on positive states are proved from the
Protocol progress lemma `deliver_progress`; coherence of the successor comes
from `coherent_recv_preserved` (via `deliver_preserves_coherent`).
-/

/-
The Problem. The Foster transport API was previously only fed assumed drift
inequalities.

Solution Structure. Define the delivery step on coherent states, the load
potential, and prove both drift laws.
-/

open scoped Classical

namespace ProtocolClassical

/-! ## Delivery Step and Potential -/

/-- One delivery step on well-typed states (identity on quiescent states). -/
noncomputable def drainFStep : FStep := fun st =>
  if hQ : Quiescent st.1.G st.1.D then st
  else
    let h := deliver_progress st.2 hQ
    ⟨⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩,
      deliver_preserves_coherent (Classical.choose_spec (Classical.choose_spec h)).1 st.2⟩

/-- Lyapunov potential: in-flight load on active edges. -/
def drainV (st : WTConfigNState) : Nat :=
  drainMeasure st.1.G st.1.D

/-- On a non-quiescent state the delivery step strictly decreases the load. -/
theorem drain_step_lt (st : WTConfigNState) (hQ : ¬ Quiescent st.1.G st.1.D) :
    drainV (drainFStep st) < drainV st := by
  unfold drainFStep drainV
  rw [dif_neg hQ]
  exact (Classical.choose_spec (Classical.choose_spec (deliver_progress st.2 hQ))).2

/-- The load never increases along a delivery step. -/
theorem drain_nonincrease (st : WTConfigNState) : drainV (drainFStep st) ≤ drainV st := by
  by_cases hQ : Quiescent st.1.G st.1.D
  · unfold drainFStep; rw [dif_pos hQ]
  · exact le_of_lt (drain_step_lt st hQ)

/-- Positive load forces a strict decrease (positive load excludes quiescence). -/
theorem drain_strict_on_pos (st : WTConfigNState) (hPos : drainV st ≠ 0) :
    drainV (drainFStep st) < drainV st := by
  apply drain_step_lt
  intro hQ
  exact hPos (drain_measure_zero_of_quiescent hQ)

/-! ## Instance -/

/-- Progress-measure components: all weight on the buffered load. -/
def drainMeasureComponents : ProgressMeasureComponents where
  typeDepth := fun _ => 0
  bufferLength := drainV
  sendPotential := fun _ => 0

/-- The protocol potential of the drain components is the load. -/
theorem protocol_v_drain (st : WTConfigNState) :
    protocolV drainMeasureComponents st = drainV st := by
  simp [protocolV, drainMeasureComponents]

/-- Fully proved Foster-Lyapunov drift assumptions for the delivery step. -/
theorem drain_foster_assumptions :
    FosterLivenessAssumptions drainFStep drainMeasureComponents where
  nonincrease_of_coherence := fun st => by
    simp only [protocol_v_drain]; exact drain_nonincrease st
  strict_on_pos_of_coherence := fun st hPos => by
    simp only [protocol_v_drain] at hPos ⊢; exact drain_strict_on_pos st hPos

end ProtocolClassical
