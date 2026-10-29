module

public import ASDExplicitGamma.Model.Q3DerivativeGram

/-! Exact global quadratic increment bound of the literal product-q3 covariance. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open Homogenization
noncomputable section

 theorem q3Cov_abs (x : ℝ) : q3Cov |x| = q3Cov x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, q3Cov_even]

 theorem q3Cov_bounds_unit {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1-(78/5:ℝ)/2*t^2 ≤ q3Cov t ∧ q3Cov t ≤ 1 := by
  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hc := q3Cov_eq_polynomial_on_unit_interval t ht ht1
  have hlo : 0 ≤ q3Cov t-(1-(78/5:ℝ)/2*t^2) := by
    have he : q3Cov t-(1-(78/5:ℝ)/2*t^2) = t^4*((143/5:ℝ)*t^0*(1-t)^9 +
      (1287/5:ℝ)*t^1*(1-t)^8 +
      (4719/5:ℝ)*t^2*(1-t)^7 +
      (9438/5:ℝ)*t^3*(1-t)^6 +
      (11583/5:ℝ)*t^4*(1-t)^5 +
      (1859/1:ℝ)*t^5*(1-t)^4 +
      (1001/1:ℝ)*t^6*(1-t)^3 +
      (351/1:ℝ)*t^7*(1-t)^2 +
      (364/5:ℝ)*t^8*(1-t)^1 +
      (34/5:ℝ)*t^9*(1-t)^0) := by rw [hc]; ring
    rw [he]
    positivity
  have hhi : 0 ≤ 1-q3Cov t := by
    have he : 1-q3Cov t = t^2*((39/5:ℝ)*t^0*(1-t)^11 +
      (429/5:ℝ)*t^1*(1-t)^10 +
      (2002/5:ℝ)*t^2*(1-t)^9 +
      (5148/5:ℝ)*t^3*(1-t)^8 +
      (8151/5:ℝ)*t^4*(1-t)^7 +
      (1716/1:ℝ)*t^5*(1-t)^6 +
      (1287/1:ℝ)*t^6*(1-t)^5 +
      (715/1:ℝ)*t^7*(1-t)^4 +
      (286/1:ℝ)*t^8*(1-t)^3 +
      (78/1:ℝ)*t^9*(1-t)^2 +
      (13/1:ℝ)*t^10*(1-t)^1 +
      (1/1:ℝ)*t^11*(1-t)^0) := by rw [hc]; ring
    rw [he]
    positivity
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

 theorem q3Cov_quadratic_bounds (x : ℝ) :
    1-(78/5:ℝ)/2*x^2 ≤ q3Cov x ∧ q3Cov x ≤ 1 := by
  by_cases hx : |x| ≤ 1
  · have h := q3Cov_bounds_unit (abs_nonneg x) hx
    simpa only [q3Cov_abs, sq_abs] using h
  · rw [q3Cov_zero_of_abs_ge_one (le_of_not_ge hx)]
    constructor
    · have hsq : 1 ≤ |x|^2 := one_le_pow₀ (le_of_not_ge hx)
      rw [sq_abs] at hsq
      nlinarith only [hsq]
    · norm_num

 theorem q3ProductCovariance_increment_bound (x : Vec 2) :
    2*(1-q3ProductCovariance x) ≤ (78/5:ℝ)*(x 0^2+x 1^2) := by
  have h0 := q3Cov_quadratic_bounds (x 0)
  have h1 := q3Cov_quadratic_bounds (x 1)
  have hp := mul_nonneg (sub_nonneg.mpr h0.2) (sub_nonneg.mpr h1.2)
  unfold q3ProductCovariance
  nlinarith only [h0.1,h1.1,hp]

end
end ASDExplicitGamma.Model
