module

public import ASDExplicitGamma.Native.HeatVHEATSourceAuxiliary

/-! The actual source-normalized finite-band moment curve and its analytic
derivative identity. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

local instance nativeHeatQ3RefinedSourceAssemblyChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The source-normalized actual complete-band moment has its exact
cancelled-generator derivative on the open heat interval. -/
theorem nativeHeatQ3RefinedCarrierSourceMoment_hasDerivAt
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ : ℝ) (hθ : 0 < θ)
    (k : ℕ) (hk : k ≠ 0) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => nativeHeatQ3RefinedCarrierSourceMoment M h hM m k θ s)
      (nativeHeatQ3RefinedCarrierSourceMomentGenerator M h hM m k θ t) t := by
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i : nativeHeatQ3RefinedCarrierIndex, MeasurableSet (U i) :=
    fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hvol : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)
  let bands := nativeHeatQ3RefinedCarrierPhysicalShells m
  let P := nativeHeatQ3RefinedCarrierOldMap m
  let L := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  have hbands : ∀ d : Fin 9, m + 1 < bands d := by
    intro d
    exact nativeHeatQ3RefinedCarrierBands_afterOldLabel m d
  have hlaw := nativeHeatQ3RefinedCarrierBandLaw M h hM m
  simpa [nativeHeatQ3RefinedCarrierSourceMoment,
    nativeHeatQ3RefinedCarrierSourceMomentGenerator,
    U, hU, hvol, bands, P, L, hA, T] using
    (nativeHeatChildBandMoment_hasDerivAt U hU hvol
      M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1
      (nativeHeatQ3RefinedCarrierDomain m) M (m + 1) bands hbands P L hA T θ hθ hlaw
      k hk ht)

end ASDExplicitGamma.Native

end
