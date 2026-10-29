module

public import ASDExplicitGamma.Gaussian.WaveGateConstants

/-! Exact variance and shell-length normalization of the Gaussian tensor estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- Restore a nonnegative amplitude and a positive physical length without a
square-root loss in either factor. -/
theorem supMean_sqrt_variance_scale (T B D : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B) (hD : 0 < D) :
    Real.sqrt (T*(B^2/D^2)) = (B/D)*Real.sqrt T := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  simp only [mul_pow, div_pow, Real.sq_sqrt hT]
  ring

/-- The standard deviation of a normalized covariance scale. -/
theorem supMean_sqrt_variance_quotient (B D : ℝ) (hB : 0 ≤ B) (hD : 0 < D) :
    Real.sqrt (B^2/D^2) = B/D := by
  simpa only [one_mul, Real.sqrt_one, mul_one] using
    supMean_sqrt_variance_scale 1 B D (by norm_num) hB hD

/-- The source operator norm constant is restored directly from its square. -/
theorem supMean_sqrt_operator_variance_scale (E B D : ℝ) (hE : 0 ≤ E) (hB : 0 ≤ B) (hD : 0 < D) :
    Real.sqrt (E^2*(B^2/D^2)) = (B/D)*E := by
  rw [supMean_sqrt_variance_scale (E^2) B D (sq_nonneg E) hB hD, Real.sqrt_sq hE]

end ASDExplicitGamma.Gaussian
