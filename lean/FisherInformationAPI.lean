import FisherInformationAPI.Core
import FisherInformationAPI.Geometry
import FisherInformationAPI.Estimation
import FisherInformationAPI.Laws
import FisherInformationAPI.MatrixLogdet
import FisherInformationAPI.Certificate
import FisherInformationAPI.Fixtures


/-! # FisherInformationAPI

Abstract API boundary for finite-discrete Fisher information geometry.

## Quick Reference

Operations:
- `Family`, `naturalParameter`, `expectationParameter`
- `logPartition`, `density`, `expectationOf`
- `score`, `fisherInformation`, `hessianLogPartition`
- `mappingNaturalToExpectation`, `mappingExpectationToNatural`, `dualPotential`
- `klBetweenParameters`, `klClosedForm`, `fisherMetric`
- `locallyUnbiasedEstimator`, `estimatorCovariance`, `fisherVolume`
- `reachabilityRegion`, `naturalGradientStep`

Laws:
- `FisherPSD`, `FisherEqHessian`, `LegendreDuality`
- `DualPotentialEqLegendre`, `KLNonneg`, `KLZeroIffEqualParameters`
- `KLSecondOrderTaylor`, `FisherMetricSymmetric`, `FisherMetricPSD`
- `CramerRaoBound`, `ReachabilityVolumeBound`, `NaturalGradientExists`

## Trust Boundary

This file states the abstract operations and law predicates. Concrete
realizations live under `FisherInformationInstance`, where law witnesses are
checked against specific finite-discrete models.
-/

/-
The Problem. Telltale has an entropy-facing analysis boundary, but no parallel
interface for finite-discrete Fisher information geometry.

Solution Structure.
1. Introduce the API namespace and keep concrete realizations out of this file.
2. Add mathematical content phase by phase behind this stable import name.
3. Mirror the `ClassicalAnalysisAPI` trust-boundary layout as the API grows.
-/

set_option autoImplicit false
