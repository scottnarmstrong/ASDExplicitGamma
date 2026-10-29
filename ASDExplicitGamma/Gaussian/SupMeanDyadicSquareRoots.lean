module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicPayments

/-! Exact half-cell square-root identities preserve the source mean and metric constants. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- Every half-cell scale is strictly positive. -/
theorem supMean_dyadic_mean_scale_pos (n : ℕ) : 0 < supMeanDyadicMeanScale n := by
  rw [supMean_dyadic_mean_scale_eq]
  positivity

/-- Every Euclidean metric scale is strictly positive. -/
theorem supMean_dyadic_metric_scale_pos (n : ℕ) : 0 < supMeanDyadicMetricScale n := by
  rw [supMean_dyadic_metric_scale_eq]
  positivity

/-- The isotropic half trace exactly cancels the planar center-increment factor two. -/
theorem supMean_dyadic_mean_root (T V s : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V) (hs : 0 ≤ s) (n : ℕ) :
    Real.sqrt ((T/2)*V*(2*s^2/((2:ℝ)^(n+2))^2)) =
      (s*Real.sqrt V)*Real.sqrt T*supMeanDyadicMeanScale n := by
  have hscale := (supMean_dyadic_mean_scale_pos n).le
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  simp only [mul_pow, Real.sq_sqrt hV, Real.sq_sqrt hT, supMean_dyadic_mean_scale_eq]
  ring

/-- The sharp Gaussian increment metric retains the Euclidean sqrt(2) factor. -/
theorem supMean_dyadic_metric_root (E V s : ℝ) (hE : 0 ≤ E) (hV : 0 ≤ V) (hs : 0 ≤ s) (n : ℕ) :
    Real.sqrt ((E^2*V)*(2*s^2/((2:ℝ)^(n+2))^2)) =
      (s*Real.sqrt V)*E*supMeanDyadicMetricScale n := by
  have hscale := (supMean_dyadic_metric_scale_pos n).le
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  simp only [supMean_dyadic_metric_scale_eq, mul_pow, div_pow, Real.sq_sqrt hV,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

end ASDExplicitGamma.Gaussian
