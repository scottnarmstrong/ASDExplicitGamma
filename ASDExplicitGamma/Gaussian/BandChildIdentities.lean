module

public import ASDExplicitGamma.Gaussian.BandBackwardCoupling
public import ASDExplicitGamma.Gaussian.ChildResponse
public import ASDExplicitGamma.Gaussian.GeneratorSplit

/-! # The literal child-product backward identities for finite fresh q3 bands -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The source test is literally W_r evaluated at the actual child medium and the independent
physical center Gaussian. This is (8.12) and (8.16), without a center/remainder independence step. -/
theorem bandModelChildBackwardAverage_eq {b : ℕ} {n : ℕ} [NeZero n]
    (U : Fin n → Set (Vec 2)) [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))]
    [∀ i, CompactSpace (closure (U i))]
    (hU : ∀ i, MeasurableSet (U i)) (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (r : ℕ)
    (K : Set (Vec 2)) [CompactSpace K] (M : ABKModel 2) (m : ℤ) (k : Fin b → ℤ)
    (P : C(K, ℝ) →L[ℝ] (∀ i, C(closure (U i), ℝ)))
    (L : C(K, ℝ) →L[ℝ] (Fin n → ℝ))
    {v : ℕ → BandHilbert b} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : BandHilbert b →L[ℝ] C(K, ℝ)) (θ t : ℝ) :
    bandModelBackwardAverage K M m k P hA (((childConstantMap (fun i => closure (U i))).comp L).comp T)
      (childPower U hU hvol ν σ hν hσ r) θ t =
      ∫ ω, ∫ η, childW U hU hvol ν σ hν hσ r
        (P (olderField K m ω + Real.sqrt t • modelBand K k ω))
        (Real.sqrt ((1 + θ) * (1 - t)) • L (gaussianSeriesLimitE hA T η))
        ∂standardGaussianInfinitePi ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold bandModelBackwardAverage bandModelAverage backwardTest gaussianSeriesHeatAverage
    gaussianSeriesHeatArgument childW gaussianSeriesLimitE
  simp only [map_add, map_smul, ContinuousLinearMap.comp_apply]

end ASDExplicitGamma.Gaussian
