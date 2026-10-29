module

public import ASDExplicitGamma.Native.HeatCooperativeBandCurve
public import ASDExplicitGamma.Native.HeatFiniteRankLimit
public import ASDExplicitGamma.Native.HeatVHEATError
public import ASDExplicitGamma.Native.HeatAffineGreen

/-! # Contract for the refined actual child heat curve

This contract is stated on the actual complete-band child moment and its
cancelled generator.  The finite band is kept whole, so its shared child
center covariance is the covariance in the generator.  `hlaw` records the
actual cutoff-law realization by the countable Gaussian series used by the
fixed-operator limit.
-/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open Filter
open scoped ENNReal Topology

/-- The actual child moment is differentiable on the open interpolation
interval, with its exact cancelled generator.  This is the analytic part of
the refined-heat contract; the quantitative VHEAT inequality is the separate
source estimate recorded by `NativeRefinedHeatConclusion`. -/
theorem nativeHeatChildBandMoment_hasDerivAt
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (hbands : ∀ i, m < bands i)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K bands) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (k : ℕ) (hk : k ≠ 0) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => nativeHeatChildBandMoment U hU hvol ν σ hν hσ
        K M m bands P L hA T k θ s)
      (nativeHeatChildBandMomentGenerator U hU hvol ν σ hν hσ
        K M m bands P L hA T k θ t) t := by
  have hreg := nativeHeat_childBandMoment_regular_of_realization
    U hU hvol ν σ hν hσ K M m bands hbands P L hA T hlaw hθ k
  simpa [nativeHeatChildBandMoment, nativeHeatChildBandMomentGenerator, hk] using
    hreg.2.2 t ht

end ASDExplicitGamma.Native
