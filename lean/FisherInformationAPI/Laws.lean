import FisherInformationAPI.Estimation

/-! # FisherInformationAPI.Laws

The law-bearing `Laws` typeclass and its re-exported theorems.

Part of the `FisherInformationAPI` boundary (finite-discrete Fisher
information geometry); re-exported by the `FisherInformationAPI` module.
-/

set_option autoImplicit false

namespace FisherInformationAPI

open scoped BigOperators Matrix MatrixOrder
open Asymptotics

noncomputable section

/-! ## Laws Typeclass And Exports -/

/-- Law-bearing Fisher information interface used by downstream modules. -/
class Laws extends Model where
  fisher_psd : FisherPSD toModel
  fisher_eq_hessian : FisherEqHessian toModel
  legendre_duality : LegendreDuality toModel
  dual_potential_eq_legendre : DualPotentialEqLegendre toModel
  kl_closed_form : KLClosedForm toModel
  kl_nonneg : KLNonneg toModel
  kl_zero_iff_equal_parameters : KLZeroIffEqualParameters toModel
  kl_second_order_taylor : KLSecondOrderTaylor toModel
  fisher_metric_symmetric : FisherMetricSymmetric toModel
  fisher_metric_psd : FisherMetricPSD toModel
  cramer_rao_bound : CramerRaoBound toModel
  reachability_volume_bound : ReachabilityVolumeBound toModel
  natural_gradient_exists : NaturalGradientExists toModel

/-- Promote `Laws` to `Model` so operation wrappers infer automatically. -/
instance (priority := 100) lawsToModel [Laws] : Model :=
  Laws.toModel

section LawsExports

variable [Laws]

/-- Re-export Fisher PSD from `Laws`. -/
theorem fisher_psd :
    FisherPSD (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_psd (self := inferInstance)

/-- Re-export Fisher-Hessian identity from `Laws`. -/
theorem fisher_eq_hessian :
    FisherEqHessian (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_eq_hessian (self := inferInstance)

/-- Re-export Legendre duality from `Laws`. -/
theorem legendre_duality :
    LegendreDuality (Laws.toModel (self := inferInstance)) :=
  Laws.legendre_duality (self := inferInstance)

/-- Re-export dual-potential closed form from `Laws`. -/
theorem dual_potential_eq_legendre :
    DualPotentialEqLegendre (Laws.toModel (self := inferInstance)) :=
  Laws.dual_potential_eq_legendre (self := inferInstance)

/-- Re-export the KL Bregman closed form from `Laws`. -/
theorem kl_closed_form :
    KLClosedForm (Laws.toModel (self := inferInstance)) :=
  Laws.kl_closed_form (self := inferInstance)

/-- Re-export KL nonnegativity from `Laws`. -/
theorem kl_nonneg :
    KLNonneg (Laws.toModel (self := inferInstance)) :=
  Laws.kl_nonneg (self := inferInstance)

/-- Re-export zero-KL parameter characterization from `Laws`. -/
theorem kl_zero_iff_equal_parameters :
    KLZeroIffEqualParameters (Laws.toModel (self := inferInstance)) :=
  Laws.kl_zero_iff_equal_parameters (self := inferInstance)

/-- Re-export second-order KL/Fisher relation from `Laws`. -/
theorem kl_second_order_taylor :
    KLSecondOrderTaylor (Laws.toModel (self := inferInstance)) :=
  Laws.kl_second_order_taylor (self := inferInstance)

/-- Re-export Fisher metric symmetry from `Laws`. -/
theorem fisher_metric_symmetric :
    FisherMetricSymmetric (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_metric_symmetric (self := inferInstance)

/-- Re-export Fisher metric PSD from `Laws`. -/
theorem fisher_metric_psd :
    FisherMetricPSD (Laws.toModel (self := inferInstance)) :=
  Laws.fisher_metric_psd (self := inferInstance)

/-- Re-export Cramer-Rao from `Laws`. -/
theorem cramer_rao_bound_law :
    CramerRaoBound (Laws.toModel (self := inferInstance)) :=
  Laws.cramer_rao_bound (self := inferInstance)

/-- Re-export reachability-volume bound from `Laws`. -/
theorem reachability_volume_bound :
    ReachabilityVolumeBound (Laws.toModel (self := inferInstance)) :=
  Laws.reachability_volume_bound (self := inferInstance)

/-- Re-export natural-gradient existence from `Laws`. -/
theorem natural_gradient_exists :
    NaturalGradientExists (Laws.toModel (self := inferInstance)) :=
  Laws.natural_gradient_exists (self := inferInstance)

end LawsExports

end

end FisherInformationAPI
