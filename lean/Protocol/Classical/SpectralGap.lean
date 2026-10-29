import Protocol.Classical.Instantiation
import Classical.Families.SpectralGapTermination

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unnecessarySimpa false

open scoped BigOperators

/-! # Protocol.Classical.SpectralGap

Deterministic-chain encoding of a protocol step `FStep` as a 0/1 stochastic
kernel on `WTConfigN`.

**Honest scope (Option B).** A deterministic kernel is a functional-graph
matrix: its eigenvalues are `0` and roots of unity, so every nontrivial
eigenvalue has modulus `0` or `1` and the spectral gap is degenerate (`0` or
`1`). Spectral-gap, Cheeger, hitting-time and product-chain statements over
this kernel were therefore vacuous restatements of assumed witnesses and have
been removed. Only the deterministic-chain facts (nonnegativity and
stochasticity of the kernel) are proved here. A meaningful spectral result
would need a genuinely stochastic (e.g. scheduler-randomised) protocol kernel.
-/

section

namespace ProtocolClassical

/-- Alias used in 2.7: well-typed coherent protocol states. -/
abbrev WTConfigN := WTConfigNState

variable [DecidableEq WTConfigN]

/-! ## Deterministic Kernel Encoding -/

/-- Deterministic one-step kernel induced by protocol step function `FStep`. -/
def wtConfigNDetTransition (step : FStep) (s s' : WTConfigN) : ℝ :=
  if s' = step s then 1 else 0

/-- The deterministic 0/1 kernel is nonnegative. -/
theorem wt_config_n_det_transition_nonneg (step : FStep) :
    ∀ s s', 0 ≤ wtConfigNDetTransition step s s' := by
  intro s s'
  by_cases h : s' = step s
  · simp [wtConfigNDetTransition, h]
  · simp [wtConfigNDetTransition, h]

variable [Fintype WTConfigN]

/-! ## Deterministic Chain -/

/-- Each row of the deterministic kernel sums to one (single `1` at `step s`). -/
theorem wt_config_n_det_transition_stochastic (step : FStep) :
    ∀ s, (∑ s', wtConfigNDetTransition step s s') = 1 := by
  intro s
  classical
  simpa [wtConfigNDetTransition] using
    (Finset.sum_ite_eq (s := (Finset.univ : Finset WTConfigN)) (a := step s) (b := (1 : ℝ)))

/-- The deterministic chain induced by `step` (degenerate spectrum; see module doc). -/
def wtConfigNDeterministicChain (step : FStep) :
    Classical.SpectralGapTermination.MarkovChain WTConfigN where
  transition := wtConfigNDetTransition step
  nonneg := wt_config_n_det_transition_nonneg step
  stochastic := wt_config_n_det_transition_stochastic step

end ProtocolClassical
