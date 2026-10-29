module

public import ASDExplicitGamma.Native.HeatVHEATRefinedStart
public import ASDExplicitGamma.Native.HeatInitialProduct
public import ASDExplicitGamma.Native.HeatInitialCrossRow
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.Heat009Initial
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Gaussian.NormalEvenMoments
public import ASDExplicitGamma.Native.HeatInitialCrossTypeTwo
public import ASDExplicitGamma.Native.HeatVHEATSourceAssembly

/-! Time-zero rows for the unscaled, source-covariance refined VHEAT carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

local instance nativeHeatQ3RefinedSourceStartIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedSourceStartChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedSourceStartChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- At backward time zero, the source-normalized depth-ten carrier is the
actual complete-band average with the source center map and covariance
`1 + θ`. -/
theorem nativeHeatQ3RefinedCarrierSourceMoment_zero_eq_actualBandAverage
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (k : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    nativeHeatQ3RefinedCarrierSourceMoment M h hM m k θ 0 =
      bandModelAverage (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
        (nativeHeatQ3RefinedCarrierPhysicalShells m)
        (nativeHeatQ3RefinedCarrierOldMap m)
        ((childConstantMap
          (fun i : nativeHeatQ3RefinedCarrierIndex =>
            closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))).comp
          (nativeHeatQ3RefinedCarrierSourceCenterMap m))
        (nativeHeatQ3RefinedCarrierPowerTest M m k) (1 + θ) := by
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hU : ∀ i, MeasurableSet (U i) :=
    fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)
  let K := nativeHeatQ3RefinedCarrierDomain m
  let bands := nativeHeatQ3RefinedCarrierPhysicalShells m
  let P := nativeHeatQ3RefinedCarrierOldMap m
  let L := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  have hbands : ∀ d : Fin 9, m + 1 < bands d := by
    intro d
    exact nativeHeatQ3RefinedCarrierBands_afterOldLabel m d
  have hstart := nativeHeatChildBandMoment_start_eq_actualBandAverage
    U hU hvol M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 K M (m + 1) bands
    hbands P L hA T hθ
    (nativeHeatQ3RefinedCarrierBandLaw M h hM m) k
  simpa only [nativeHeatQ3RefinedCarrierSourceMoment,
    nativeHeatQ3RefinedCarrierPowerTest,
    U, hU, hvol, K, bands, P, L, hA, T] using hstart

end ASDExplicitGamma.Native

end
