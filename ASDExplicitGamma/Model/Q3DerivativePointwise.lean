module

public import ASDExplicitGamma.Model.Q3DerivativeBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-! Sharp global scalar-gradient and product-Hessian bounds, from the actual covariance jets. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open Set
noncomputable section

 theorem q3Cov_second_abs_le (x : ℝ) : |iteratedDeriv 2 q3Cov x| ≤ (78/5:ℝ) := by
  have hh := q3Cov_derivative_combined x
  apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 78/5)).1
  rw [sq_abs]
  nlinarith only [hh, sq_nonneg (iteratedDeriv 1 q3Cov x)]

 theorem q3Cov_first_abs_le (x : ℝ) : |deriv q3Cov x| ≤ (78/5:ℝ)*|x| := by
  have hd : ContDiff ℝ 1 (deriv q3Cov) := q3Cov_contDiff_two.deriv'
  have hb := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hd.differentiable (by norm_num)) t)
    (fun t _ => by simpa only [Real.norm_eq_abs, show (2:ℕ)=1+1 by rfl,
      iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using q3Cov_second_abs_le t)
    (mem_univ (0:ℝ)) (mem_univ x)
  have h0 : deriv q3Cov 0 = 0 := by simpa only [iteratedDeriv_one] using q3Cov_odd_derivatives_zero.1
  simpa only [h0, sub_zero, Real.norm_eq_abs] using hb

 theorem q3CovProduct_hessian_sq_le (x y : ℝ) :
    ((iteratedDeriv 2 q3Cov x)*q3Cov y)^2 + 2*(deriv q3Cov x*deriv q3Cov y)^2 +
      (q3Cov x*(iteratedDeriv 2 q3Cov y))^2 ≤ 2*(78/5:ℝ)^2 := by
  have hx := q3Cov_derivative_combined x
  have hy := q3Cov_derivative_combined y
  simp only [iteratedDeriv_one] at hx hy
  have hdx : (deriv q3Cov x)^2 ≤ (78/5:ℝ) := by nlinarith only [hx,sq_nonneg (iteratedDeriv 2 q3Cov x)]
  have hdy : (deriv q3Cov y)^2 ≤ (78/5:ℝ) := by nlinarith only [hy,sq_nonneg (iteratedDeriv 2 q3Cov y)]
  have hp := mul_nonneg (sq_nonneg (deriv q3Cov x)) (sub_nonneg.mpr hdy)
  have hq := mul_nonneg (sq_nonneg (deriv q3Cov y)) (sub_nonneg.mpr hdx)
  have hxy := mul_le_mul_of_nonneg_left (q3Cov_sq_le_one y) (sq_nonneg (iteratedDeriv 2 q3Cov x))
  have hyx := mul_le_mul_of_nonneg_left (q3Cov_sq_le_one x) (sq_nonneg (iteratedDeriv 2 q3Cov y))
  simp only [mul_pow]
  nlinarith only [hx,hy,hp,hq,hxy,hyx]

end
end ASDExplicitGamma.Model
