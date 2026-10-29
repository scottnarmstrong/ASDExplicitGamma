module

public import ASDExplicitGamma.Gaussian.Q3WeightedPointVariance
public import ASDExplicitGamma.Gaussian.SpatialMeanMoment

/-! # Uniform spatial mean bounds for orthogonal projections of the physical band -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β w : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

/-- The literal retained ordinary-H³ band, observed as a weighted continuous spatial field. -/
noncomputable def q3WeightedBandPartialValue (N : ℕ) (ω : ℕ → ℝ) :
    C(closedRectangle a b c d, ℝ) :=
  q3WeightedBandH3Value a b c d β w L
    (gaussianPartialSum (q3BandH3Directions a b c d β L) N ω)

/-- Every partial field retains all finite probability moments from its ordinary-H³ carrier. -/
theorem memLp_q3WeightedBandPartialValue {p : ℝ} (hp : 2 ≤ p) (N : ℕ) :
    MemLp (q3WeightedBandPartialValue a b c d β w L N) (ENNReal.ofReal p) standardGaussianInfinitePi := by
  have hh := @memLp_gaussianPartialSum (Q3BandH3 a b c d β L) inferInstance
    (instQ3BandH3InnerProductSpace a b c d β L) inferInstance inferInstance inferInstance
    inferInstance (q3BandH3Directions a b c d β L) p hp
    (q3BandH3Directions_summable a b c d β L) N
  exact @MemLp.continuousLinearMap_comp (ℕ → ℝ) ℝ (Q3BandH3 a b c d β L)
    C(closedRectangle a b c d, ℝ) inferInstance (ENNReal.ofReal p) standardGaussianInfinitePi
    inferInstance inferInstance inferInstance (instQ3BandH3NormedSpace a b c d β L) inferInstance
    (gaussianPartialSum (q3BandH3Directions a b c d β L) N) hh
    (q3WeightedBandH3Value a b c d β w L)

/-- At every point, a retained physical band is a scalar normal with its retained variance. -/
theorem q3WeightedBandPartialValue_point_law (x : closedRectangle a b c d) (N : ℕ) :
    standardGaussianInfinitePi.map (fun ω => q3WeightedBandPartialValue a b c d β w L N ω x) =
      gaussianReal 0 (Real.toNNReal (∑ j ∈ Finset.range N,
        (q3WeightedBandH3Value a b c d β w L (q3BandH3Directions a b c d β L j) x) ^ 2)) := by
  have he : (fun ω => q3WeightedBandPartialValue a b c d β w L N ω x) =
      gaussianScalarPartialSum (fun j => q3WeightedBandH3Value a b c d β w L
        (q3BandH3Directions a b c d β L j) x) N := by
    funext ω
    simp only [q3WeightedBandPartialValue, gaussianPartialSum, gaussianScalarPartialSum,
      map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [he, map_gaussianScalarPartialSum]

/-- The retained pointwise fourth moment is uniformly bounded by the full physical variance. -/
theorem q3WeightedBandPartialValue_fourthMoment_le (hab : a < b) (hcd : c < d)
    (x : closedRectangle a b c d) (N : ℕ) :
    (∫ ω, q3WeightedBandPartialValue a b c d β w L N ω x ^ 4 ∂standardGaussianInfinitePi) ≤
      3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2 := by
  let S := ∑ j ∈ Finset.range N,
    (q3WeightedBandH3Value a b c d β w L (q3BandH3Directions a b c d β L j) x) ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm := (ContinuousMap.evalCLM ℝ x).continuous.comp_aestronglyMeasurable
    (memLp_q3WeightedBandPartialValue a b c d β w L (p := 4) (by norm_num) N).aestronglyMeasurable
  have he : (∫ ω, q3WeightedBandPartialValue a b c d β w L N ω x ^ 4 ∂standardGaussianInfinitePi) =
      3 * S ^ 2 := by
    rw [← integral_map (φ := fun ω => q3WeightedBandPartialValue a b c d β w L N ω x)
      (f := fun r : ℝ => r ^ (4 : ℕ)) hm.aemeasurable (by fun_prop),
      q3WeightedBandPartialValue_point_law, integral_gaussianReal_pow_four, Real.coe_toNNReal _ hS]
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hS (q3WeightedBandH3Value_partial_variance_le a b c d β w L hab hcd x N) 2)
    (by norm_num : (0 : ℝ) ≤ 3)

/-- The probability mean of every spatial norm projection has the exact uniform fourth-moment cap. -/
theorem q3WeightedBandPartialValue_spatial_mean_sq_le (hab : a < b) (hcd : c < d) (N : ℕ) :
    (∫ ω, ‖ContinuousMap.toLp 4 (spatialVolume (closedRectangle a b c d)) ℝ
      (q3WeightedBandPartialValue a b c d β w L N ω)‖ ∂standardGaussianInfinitePi) ^ 2 ≤
      Real.sqrt ((spatialVolume (closedRectangle a b c d)).real Set.univ *
        (3 * (∑ i, w i ^ 2 * β i ^ 2) ^ 2)) := by
  exact spatialLp4_mean_sq_le_of_point_moment standardGaussianInfinitePi _ _
    (by simpa only [ENNReal.ofReal_ofNat] using
      memLp_q3WeightedBandPartialValue a b c d β w L (p := 4) (by norm_num) N)
    (fun x => q3WeightedBandPartialValue_fourthMoment_le a b c d β w L hab hcd x N)

end
end ASDExplicitGamma.Gaussian
