import Mathlib
import Classical.FosterLyapunovHarris
import Classical.MaxWeightBackpressure
import Classical.LargeDeviationPrinciple
import Classical.PropagationOfChaos
import Classical.HeavyTrafficDiffusion
import Classical.MixingTimeBounds
import Classical.FluidLimitStability
import Classical.ConcentrationInequalities
import Classical.LittlesLaw
import Classical.FunctionalCLT

/-! # Classical.Transport

Single-file facade for transported-theorem APIs.
Downstream modules should import this module instead of theorem-family internals.
-/

namespace Classical
namespace Transport

universe u

/- Core transport context shared by all theorem families. -/
structure TransportCtx (State : Type u) where
  step : State → State
  coherent : State → Prop
  harmony : Prop
  finiteState : Prop

/- Family-specific transport inputs and output contracts. -/
structure FosterInput (State : Type u) (ctx : TransportCtx State) where
  system : FosterLyapunovHarris.DriftSystem State
  step_agrees : system.step = ctx.step

def FosterConclusion {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) : Prop :=
  ∀ s n, input.system.V (input.system.step^[n] s) ≤ input.system.V s

structure MaxWeightInput (ι : Type) [Fintype ι] where
  q : ι → Real
  choice : MaxWeightBackpressure.MaxWeightChoice q

def MaxWeightConclusion {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) : Prop :=
  ∀ ν : ι → Real,
    MaxWeightBackpressure.weight input.q ν ≤
      MaxWeightBackpressure.weight input.q input.choice.sched

structure LDPInput where
  p : Nat → Real
  witness : LargeDeviationPrinciple.LDPWitness p

def LDPConclusion (input : LDPInput) : Prop :=
  ∀ n, input.p (n + 1) ≤
    LargeDeviationPrinciple.exponentialEnvelope input.witness.C input.witness.ρ n

structure MeanFieldInput (n : Nat) where
  x : Fin n → Real

def MeanFieldConclusion {n : Nat} (input : MeanFieldInput n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    PropagationOfChaos.empiricalMean (fun i => input.x (σ i)) =
      PropagationOfChaos.empiricalMean input.x

structure HeavyTrafficInput where
  σ : Real
  n : Nat

def HeavyTrafficConclusion (input : HeavyTrafficInput) : Prop :=
  (input.σ * HeavyTrafficDiffusion.diffusionScale input.n) ^ 2 = input.σ ^ 2 * input.n

structure MixingInput where
  d : Nat → Real
  witness : MixingTimeBounds.MixingWitness d

def MixingConclusion (input : MixingInput) : Prop :=
  ∀ n, input.d (n + 1) ≤ MixingTimeBounds.geometricEnvelope input.witness.C input.witness.ρ n

structure FluidInput where
  x : Nat → Real
  witness : FluidLimitStability.FluidDescentWitness x

def FluidConclusion (input : FluidInput) : Prop :=
  ∀ n, FluidLimitStability.energy input.x (n + 1) ≤ FluidLimitStability.energy input.x n

structure ConcentrationInput where
  p : Real → Real
  witness : ConcentrationInequalities.ConcentrationWitness p

def ConcentrationConclusion (input : ConcentrationInput) : Prop :=
  input.p 0 ≤ 2

abbrev LittlesLawInput := LittlesLaw.LittleInput

def LittlesLawConclusion (input : LittlesLawInput) : Prop :=
  input.L = input.lam * input.W

structure FunctionalCLTInput where
  c : Real
  N : Nat
  t : Nat
  N_ne_zero : N ≠ 0

def FunctionalCLTConclusion (input : FunctionalCLTInput) : Prop :=
  FunctionalCLT.scaledProcess (fun _ => input.c) input.c input.N input.t = 0

/- Facade theorem wrappers: each exported theorem discharges its contract from
   the corresponding family-level witness/lemma. -/
theorem transported_fosterLyapunov {State : Type u} {ctx : TransportCtx State}
    (input : FosterInput State ctx) :
    FosterConclusion input := by
  intro s n
  exact FosterLyapunovHarris.DriftSystem.iterate_nonincrease (S := input.system) s n

theorem transported_maxWeight {ι : Type} [Fintype ι]
    (input : MaxWeightInput ι) :
    MaxWeightConclusion input := by
  intro ν
  exact input.choice.optimal ν

theorem transported_ldp (input : LDPInput) :
    LDPConclusion input := by
  intro n
  exact LargeDeviationPrinciple.one_step_tightening input.witness n

theorem transported_meanField {n : Nat} (input : MeanFieldInput n) :
    MeanFieldConclusion input := by
  intro σ
  exact PropagationOfChaos.empiricalMean_perm (σ := σ) (x := input.x)

theorem transported_heavyTraffic (input : HeavyTrafficInput) :
    HeavyTrafficConclusion input := by
  simpa [HeavyTrafficConclusion] using
    HeavyTrafficDiffusion.variance_scaling input.σ input.n

theorem transported_mixing (input : MixingInput) :
    MixingConclusion input := by
  intro n
  exact MixingTimeBounds.one_step_bound input.witness n

theorem transported_fluidLimit (input : FluidInput) :
    FluidConclusion input := by
  intro n
  exact FluidLimitStability.nonincreasing_energy input.witness n

theorem transported_concentration (input : ConcentrationInput) :
    ConcentrationConclusion input := by
  exact ConcentrationInequalities.at_zero_bound input.witness

theorem transported_littlesLaw (input : LittlesLawInput) :
    LittlesLawConclusion input := by
  exact LittlesLaw.queue_length input

theorem transported_functionalCLT (input : FunctionalCLTInput) :
    FunctionalCLTConclusion input := by
  simpa [FunctionalCLTConclusion] using
    FunctionalCLT.scaledProcess_const_zero input.c input.N input.t input.N_ne_zero

end Transport
end Classical
