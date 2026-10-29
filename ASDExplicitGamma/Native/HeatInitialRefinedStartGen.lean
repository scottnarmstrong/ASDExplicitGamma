module

public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceStart
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen

/-! Time-zero rows for the `ns`-shell, unscaled, source-covariance refined VHEAT
carrier, for an arbitrary Gaussian-series realization of the shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

local instance nativeHeatQ3RefinedSourceStartGenIndexNeZeroGen :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedSourceStartGenChildCompactGen (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedSourceStartGenChildFiniteGen (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- At backward time zero, the `ns`-shell source-normalized depth-ten carrier is the
actual complete-band average with the source center map and covariance `1 + θ`. -/
theorem nativeHeatQ3RefinedCarrierSourceMoment_zero_eq_actualBandAverageGen
    (ns : ℕ) [NeZero ns] (M : ABKModel 2) (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns)
    (k : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    nativeHeatQ3RefinedCarrierSourceMomentGen M m ns Ffam k θ 0 =
      bandModelAverage (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns)
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
  let bands := nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns
  let P := nativeHeatQ3RefinedCarrierOldMap m
  let L := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let hA := nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  let T := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  have hbands : ∀ d : Fin ns, m + 1 < bands d :=
    fun d => nativeHeatQ3RefinedCarrierPhysicalShellsGen_gt m d
  have hstart := nativeHeatChildBandMoment_start_eq_actualBandAverage
    U hU hvol M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 K M (m + 1) bands
    hbands P L hA T hθ
    (nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen Ffam) k
  simpa only [nativeHeatQ3RefinedCarrierSourceMomentGen,
    nativeHeatQ3RefinedCarrierPowerTest,
    U, hU, hvol, K, bands, P, L, hA, T] using hstart

end ASDExplicitGamma.Native
