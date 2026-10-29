module

public import ASDExplicitGamma.Gaussian.Q3WeightedBandLaw
public import ASDExplicitGamma.Gaussian.NormalScaledMoments

/-! # The exact point variance of an attenuated physical shell band -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open scoped NNReal

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β w : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

/-- Independent shell variances add exactly, with their deterministic squared attenuations. -/
theorem q3WeightedBandH3Value_point_variance (hab : a < b) (hcd : c < d)
    (x : closedRectangle a b c d) :
    (∑' j, (q3WeightedBandH3Value a b c d β w L
      (q3BandH3Directions a b c d β L j) x) ^ 2) = ∑ i, w i ^ 2 * β i ^ 2 := by
  let V := fun i : Fin n => Q3H3Range a b c d (β i) (L i)
  let v := fun i : Fin n => q3H3Directions a b c d (β i) (L i) whiteBasis
  let T := fun i : Fin n => w i • q3H3RangeValue a b c d (β i) (L i)
  have hf := @finiteFactor_covariance n V (fun _ => inferInstance)
    (fun i => (instQ3H3RangeInnerProductSpace a b c d (β i) (L i)).toNormedSpace)
    inferInstance C(closedRectangle a b c d, ℝ) inferInstance inferInstance v
    (fun i => q3H3Directions_summable a b c d (β i) (L i) whiteBasis) T
    (ContinuousMap.evalCLM ℝ x)
  change (∑' j, (q3WeightedBandH3Value a b c d β w L
    (q3BandH3Directions a b c d β L j) x) ^ 2) = _ at hf
  rw [hf]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑' j, (w i * (q3H3RangeValue a b c d (β i) (L i) (v i j) x)) ^ 2) = _
  simp_rw [mul_pow, tsum_mul_left]
  congr 1
  have hc0 : q3Cov 0 = 1 := by
    rw [q3Cov]
    simpa only [add_zero, ← sq] using Model.q3Kernel_sq_integral
  have hh := q3H3Directions_covariance a b c d (β i) hab hcd (L i) whiteBasis x x
  simpa only [← sq, sub_self, zero_div, hc0, mul_one] using hh

/-- Every finite noise projection has no more than the total physical point variance. -/
theorem q3WeightedBandH3Value_partial_variance_le (hab : a < b) (hcd : c < d)
    (x : closedRectangle a b c d) (N : ℕ) :
    (∑ j ∈ Finset.range N, (q3WeightedBandH3Value a b c d β w L
      (q3BandH3Directions a b c d β L j) x) ^ 2) ≤ ∑ i, w i ^ 2 * β i ^ 2 := by
  have hs := @summable_sq_norm_gaussianDirections
    (Q3BandH3 a b c d β L) ℝ inferInstance
    (instQ3BandH3NormedSpace a b c d β L) inferInstance inferInstance
    (q3BandH3Directions a b c d β L)
    (q3BandH3Directions_summable a b c d β L)
    ((ContinuousMap.evalCLM ℝ x).comp (q3WeightedBandH3Value a b c d β w L))
  simp only [ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply, Real.norm_eq_abs, sq_abs] at hs
  rw [← q3WeightedBandH3Value_point_variance a b c d β w L hab hcd x]
  exact hs.sum_le_tsum (Finset.range N) (fun _ _ => sq_nonneg _)

end
end ASDExplicitGamma.Gaussian
