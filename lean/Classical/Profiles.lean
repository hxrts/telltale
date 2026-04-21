import Classical.Transport.Contracts

set_option autoImplicit false

/-! # Classical Profile Constructors

Semantic constructors for transported classical theorem inputs.

These helpers build transport inputs from family-level assumptions and witnesses.
They do not store final theorem conclusions; downstream theorem packs still derive
conclusions through `Classical.Transport.Theorems`.
-/

namespace Classical
namespace Transport

universe u

variable [EntropyAPI.AnalysisLaws]

/-- Build a Foster-Lyapunov input from a drift system and step agreement. -/
def mkFosterInput
    {State : Type u} {ctx : TransportCtx State}
    (system : FosterLyapunovHarris.DriftSystem State)
    (step_agrees : system.step = ctx.step) :
    FosterInput State ctx :=
  { system := system
  , step_agrees := step_agrees
  }

/-- Build a MaxWeight input from an optimal protocol schedule. -/
def mkMaxWeightInput
    {ι : Type} [Fintype ι]
    (q : ι → Real)
    (sched : ι → Real)
    (optimal : ∀ ν : ι → Real,
      MaxWeightBackpressure.weight q ν ≤ MaxWeightBackpressure.weight q sched) :
    MaxWeightInput ι :=
  { q := q
  , choice :=
      { sched := sched
      , optimal := optimal
      }
  }

/-- Build a large-deviation input from an exponential-tail witness. -/
def mkLDPInput
    (p : Nat → Real)
    (witness : LargeDeviationPrinciple.LDPWitness p) :
    LDPInput :=
  { p := p
  , witness := witness
  }

/-- Build a mean-field input from a finite population state. -/
def mkMeanFieldInput
    {n : Nat}
    (x : Fin n → Real) :
    MeanFieldInput n :=
  { x := x }

/-- Build a heavy-traffic input from a diffusion parameter and scaling horizon. -/
def mkHeavyTrafficInput
    (σ : Real)
    (n : Nat) :
    HeavyTrafficInput :=
  { σ := σ
  , n := n
  }

/-- Build a mixing-time input from a geometric mixing witness. -/
def mkMixingInput
    (d : Nat → Real)
    (witness : MixingTimeBounds.MixingWitness d) :
    MixingInput :=
  { d := d
  , witness := witness
  }

/-- Build a fluid-limit input from a descent witness. -/
def mkFluidInput
    (x : Nat → Real)
    (witness : FluidLimitStability.FluidDescentWitness x) :
    FluidInput :=
  { x := x
  , witness := witness
  }

/-- Build a concentration input from a sub-Gaussian tail witness. -/
def mkConcentrationInput
    (p : Real → Real)
    (witness : ConcentrationInequalities.ConcentrationWitness p) :
    ConcentrationInput :=
  { p := p
  , witness := witness
  }

/-- Build a Little's-law input from steady-state queueing quantities. -/
def mkLittlesLawInput
    (lam W L : Real)
    (law : L = lam * W) :
    LittlesLawInput :=
  { lam := lam
  , W := W
  , L := L
  , law := law
  }

/-- Build a functional-CLT input for the constant centering instance. -/
def mkFunctionalCLTInput
    (c : Real)
    (N t : Nat)
    (N_ne_zero : N ≠ 0) :
    FunctionalCLTInput :=
  { c := c
  , N := N
  , t := t
  , N_ne_zero := N_ne_zero
  , path_eq_const := rfl
  , mean_eq_const := rfl
  }

/-- Build a spectral-gap termination input from chain, gap, and termination witnesses. -/
def mkSpectralGapInput
    {State : Type u} [Fintype State] [DecidableEq State]
    (chain : SpectralGapTermination.MarkovChain State)
    (gap_pos : SpectralGapTermination.SpectralGapPos chain)
    (termination : SpectralGapTermination.TerminationWitness chain) :
    SpectralGapInput State :=
  { chain := chain
  , gap_pos := gap_pos
  , termination := termination
  }

end Transport
end Classical
