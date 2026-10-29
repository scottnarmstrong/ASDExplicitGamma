module

public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly

/-! The VHEAT source-normalized refined carrier. The center map is the
unscaled physical child-center observation required by the source variance. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

/-- The source center map is the actual, unscaled child-center vector. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceCenterMap (m : ℤ) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (nativeHeatQ3RefinedCarrierIndex → ℝ) :=
  childCenterMap (nativeHeatQ3RefinedCarrierCenter m)

/-- The source-normalized complete-band moment, using the actual center map
and the source auxiliary covariance `(1 + θ) * (1 - t)`. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceMoment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (k : ℕ) (θ t : ℝ) : ℝ :=
  nativeHeatChildBandMoment
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
    (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
    (nativeHeatQ3RefinedCarrierPhysicalShells m)
    (nativeHeatQ3RefinedCarrierOldMap m)
    (nativeHeatQ3RefinedCarrierSourceCenterMap m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)
    k θ t

/-- The exact canceled generator of the source-normalized complete-band
moment. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceMomentGenerator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (k : ℕ) (θ t : ℝ) : ℝ :=
  nativeHeatChildBandMomentGenerator
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
    (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
    (nativeHeatQ3RefinedCarrierPhysicalShells m)
    (nativeHeatQ3RefinedCarrierOldMap m)
    (nativeHeatQ3RefinedCarrierSourceCenterMap m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)
    k θ t

end ASDExplicitGamma.Native
