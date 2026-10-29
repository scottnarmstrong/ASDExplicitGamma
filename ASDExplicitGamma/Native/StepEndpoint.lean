module

public import ASDExplicitGamma.Native.HeatTrueFrameCurve
public import ASDExplicitGamma.Native.HeatCooperativeBandCurve

/-! The endpoint of the actual finite-band child-moment path. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- At the terminal time, the auxiliary backward Gaussian has zero variance.
The cooperative moment is therefore the actual finite-band average of the
child-power test; the center map and generator representation no longer
appear in the endpoint value. -/
theorem nativeHeatChildBandMoment_one_eq_actualBandAverage
    {b n : ℕ} [NeZero b] [NeZero n]
    (U : Fin n → Set (Vec 2))
    [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (m : ℤ) (bands : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) (r : ℕ) (θ : ℝ) :
    nativeHeatChildBandMoment U hU hvol ν σ hν hσ K M m bands P L hA T
      r θ 1 =
      bandModelAverage K M m bands P P
        (childPower U hU hvol ν σ hν hσ r) 1 := by
  simp [nativeHeatChildBandMoment, bandModelBackwardAverage,
    bandModelAverage, backwardTest, gaussianSeriesHeatAverage,
    gaussianSeriesHeatArgument]

end ASDExplicitGamma.Native
