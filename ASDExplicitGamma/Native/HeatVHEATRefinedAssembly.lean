module

public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransport
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficients
public import ASDExplicitGamma.Native.HeatVHEATRefinedAuxiliary
public import ASDExplicitGamma.Native.RefinedHeatConclusion

/-! Bind the refined depth-ten carrier to the actual complete-band heat moment
and its affine Green recurrence. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

/-- The complete physical shell band of the refined depth-ten carrier has
its selected direct-sum Gaussian-series law. -/
theorem nativeHeatQ3RefinedCarrierBandLaw
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map
        (modelBand (nativeHeatQ3RefinedCarrierDomain m)
          (nativeHeatQ3RefinedCarrierPhysicalShells m)) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE
          (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)) :=
  nativeHeatQ3RefinedCarrierFreshShellSeriesLaw M h hM m

/-- Every physical refined shell is strictly after the completed OLD cutoff
label associated with the child scale `m`. -/
theorem nativeHeatQ3RefinedCarrierBands_afterOldLabel (m : ℤ) (d : Fin 9) :
    m + 1 < nativeHeatQ3RefinedCarrierPhysicalShells m d := by
  simp only [nativeHeatQ3RefinedCarrierPhysicalShells]
  omega

end ASDExplicitGamma.Native
