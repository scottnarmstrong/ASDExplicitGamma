module

public import ASDExplicitGamma.Gaussian.SeriesLawVariance
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLaw

/-! The actual auxiliary child-center Gaussian coordinates for the refined
backward heat path. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- The normalized scalar observation of the selected refined-band Gaussian
series at one actual child center. The factor `sqrt (1-t)` is the auxiliary
variance in the backward heat coupling. -/
noncomputable def nativeHeatQ3RefinedCarrierAuxCenterObservation
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] ℝ :=
  (Real.sqrt (1 - t) / (Annealed.sigmaBar M (m + 1) : ℝ)) •
    ContinuousMap.evalCLM ℝ (nativeHeatQ3RefinedCarrierCenter m i)

/-- The auxiliary scalar coordinate used by the translated source trace. -/
noncomputable def nativeHeatQ3RefinedCarrierAuxCenterGaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (t : ℝ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ξ : ℕ → ℝ) : ℝ :=
  (Annealed.sigmaBar M (m + 1) : ℝ) *
    nativeHeatQ3RefinedCarrierAuxCenterObservation M m t i
      (gaussianSeriesLimitE
        (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m) ξ)

end ASDExplicitGamma.Native
