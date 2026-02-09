import Classical.Transport

set_option autoImplicit false

/-! # Consensus.Certified

Thin wrappers around transported Classical theorem APIs.
-/

namespace Consensus
namespace Certified

universe u

theorem fosterLyapunov {State : Type u}
    {ctx : Classical.Transport.TransportCtx State}
    (input : Classical.Transport.FosterInput State ctx) :
    Classical.Transport.FosterConclusion input :=
  Classical.Transport.transported_fosterLyapunov input

theorem maxWeight {ι : Type} [Fintype ι]
    (input : Classical.Transport.MaxWeightInput ι) :
    Classical.Transport.MaxWeightConclusion input :=
  Classical.Transport.transported_maxWeight input

theorem largeDeviation
    (input : Classical.Transport.LDPInput) :
    Classical.Transport.LDPConclusion input :=
  Classical.Transport.transported_ldp input

theorem meanField {n : Nat}
    (input : Classical.Transport.MeanFieldInput n) :
    Classical.Transport.MeanFieldConclusion input :=
  Classical.Transport.transported_meanField input

theorem heavyTraffic
    (input : Classical.Transport.HeavyTrafficInput) :
    Classical.Transport.HeavyTrafficConclusion input :=
  Classical.Transport.transported_heavyTraffic input

theorem mixing
    (input : Classical.Transport.MixingInput) :
    Classical.Transport.MixingConclusion input :=
  Classical.Transport.transported_mixing input

theorem fluidLimit
    (input : Classical.Transport.FluidInput) :
    Classical.Transport.FluidConclusion input :=
  Classical.Transport.transported_fluidLimit input

theorem concentration
    (input : Classical.Transport.ConcentrationInput) :
    Classical.Transport.ConcentrationConclusion input :=
  Classical.Transport.transported_concentration input

theorem littlesLaw
    (input : Classical.Transport.LittlesLawInput) :
    Classical.Transport.LittlesLawConclusion input :=
  Classical.Transport.transported_littlesLaw input

theorem functionalCLT
    (input : Classical.Transport.FunctionalCLTInput) :
    Classical.Transport.FunctionalCLTConclusion input :=
  Classical.Transport.transported_functionalCLT input

end Certified
end Consensus

