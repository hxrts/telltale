import Protocol.Classical.Instantiation
import Classical.Families.SpectralGapTermination

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped BigOperators

section

namespace ProtocolClassical

open Classical.SpectralGapTermination

/-- Alias used in 2.7: well-typed coherent protocol states. -/
abbrev WTConfigN := WTConfigNState

variable [DecidableEq WTConfigN]

/-- Deterministic one-step kernel induced by protocol step function `FStep`. -/
def wtConfigNDetTransition (step : FStep) (s s' : WTConfigN) : ℝ :=
  if s' = step s then 1 else 0

theorem wtConfigNDetTransition_nonneg (step : FStep) :
    ∀ s s', 0 ≤ wtConfigNDetTransition step s s' := by
  intro s s'
  by_cases h : s' = step s
  · simp [wtConfigNDetTransition, h]
  · simp [wtConfigNDetTransition, h]

variable [Fintype WTConfigN]

theorem wtConfigNDetTransition_stochastic (step : FStep) :
    ∀ s, (∑ s', wtConfigNDetTransition step s s') = 1 := by
  intro s
  classical
  simpa [wtConfigNDetTransition] using
    (Finset.sum_ite_eq (s := (Finset.univ : Finset WTConfigN)) (a := step s) (b := (1 : ℝ)))

/-- 2.7 task: instantiate `MarkovChain` against `WTConfigN`. -/
def wtConfigNMarkovChain (step : FStep) :
    Classical.SpectralGapTermination.MarkovChain WTConfigN where
  transition := wtConfigNDetTransition step
  nonneg := wtConfigNDetTransition_nonneg step
  stochastic := wtConfigNDetTransition_stochastic step

/-- 2.7 task: protocol-level Cheeger inequality over the `WTConfigN` chain. -/
theorem wtConfigN_cheeger_inequality (step : FStep)
    (hGap : 0 ≤ spectralGap (wtConfigNMarkovChain step))
    (w : ConductanceWitness (wtConfigNMarkovChain step)) :
    (conductance (wtConfigNMarkovChain step) w) ^ 2 / 2 ≤
      spectralGap (wtConfigNMarkovChain step) := by
  simpa using cheeger_inequality (mc := wtConfigNMarkovChain step) hGap w

/-- Strict positivity of protocol spectral gap from `|λ₂| < 1`. -/
theorem wtConfigN_spectralGap_pos (step : FStep)
    (h : SpectralGapPos (wtConfigNMarkovChain step)) :
    0 < spectralGap (wtConfigNMarkovChain step) := by
  simpa using spectralGap_pos (mc := wtConfigNMarkovChain step) h

/-- Existence of a stationary distribution from an explicit protocol witness. -/
theorem wtConfigN_exists_stationary_dist (step : FStep)
    (w : StationaryWitness (wtConfigNMarkovChain step)) :
    ∃ π : WTConfigN → ℝ,
      IsProbabilityDist π ∧ IsStationary (wtConfigNMarkovChain step) π := by
  simpa using exists_stationary_dist (mc := wtConfigNMarkovChain step) w

/-- Hitting-time spectral upper bound specialized to protocol states. -/
theorem wtConfigN_hitting_time_spectral_bound (step : FStep)
    (hGap : 0 < spectralGap (wtConfigNMarkovChain step))
    (w : HittingTimeWitness (wtConfigNMarkovChain step)) :
    ∀ st, expectedHittingTime w st ≤ 1 / spectralGap (wtConfigNMarkovChain step) := by
  simpa using hitting_time_spectral_bound (mc := wtConfigNMarkovChain step) hGap w

/-- Expected termination-time bound specialized to protocol states. -/
theorem wtConfigN_expected_termination_bound (step : FStep)
    (hGap : 0 < spectralGap (wtConfigNMarkovChain step))
    (w : TerminationWitness (wtConfigNMarkovChain step)) :
    ∀ st, expectedTerminationTime w st ≤ 1 / spectralGap (wtConfigNMarkovChain step) := by
  simpa using expected_termination_bound (mc := wtConfigNMarkovChain step) hGap w

/-- Independent-session spectral-gap lower bound for two protocol kernels. -/
theorem wtConfigN_independent_sessions_spectral_gap
    (step₁ step₂ : FStep)
    (w : IndependentSessionsWitness
      (wtConfigNMarkovChain step₁)
      (wtConfigNMarkovChain step₂)) :
    min (spectralGap (wtConfigNMarkovChain step₁))
        (spectralGap (wtConfigNMarkovChain step₂)) ≤
      spectralGap w.productChain := by
  simpa using independent_sessions_spectral_gap
    (mc₁ := wtConfigNMarkovChain step₁)
    (mc₂ := wtConfigNMarkovChain step₂) w

end ProtocolClassical
