module

public import ASDExplicitGamma.Native.OldSignedDerivativeConstants
public import ASDExplicitGamma.Triadic.HilbertPoincareNumerics

/-! Certified outward q3 derivative-row constants in AN (3.3). The final
2.665 cap uses the sharper internal linear coefficient, rather than
incorrectly inferring it from the outward 2.515 polynomial alone. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Triadic
noncomputable section

/-- The dimensionless actual q3 derivative-only row coefficient. -/
def oldSignedDerivativeShape (rho : ℝ) : ℝ :=
  (2/Real.pi)*rho*Real.sqrt (78/5:ℝ)+
    planarC0*planarC1*rho^2*Real.sqrt (23244/25:ℝ)

/-- A slightly sharper internal linear cap certifies the final 2.665. -/
theorem old_signed_derivative_linear_cap :
    (2/Real.pi)*Real.sqrt (78/5:ℝ)<(5029/2000:ℝ) := by
  have hr : Real.sqrt (78/5:ℝ)<(987421/250000:ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤78/5),Real.sqrt_nonneg (78/5:ℝ)]
  have hp : (314159/100000:ℝ)<Real.pi := by linarith only [Real.pi_gt_d20]
  rw [div_mul_eq_mul_div,div_lt_iff₀ Real.pi_pos]
  nlinarith only [hr,hp]

/-- The second-row eigenvalue gives the source's outward 4.062 cap. -/
theorem old_signed_derivative_quadratic_cap :
    planarC0*planarC1*Real.sqrt (23244/25:ℝ)≤(2031/500:ℝ) := by
  have h0 := planarC0_decimal_bounds.2.le
  have h1 := planarC1_decimal_bounds.2.le
  have hr : Real.sqrt (23244/25:ℝ)≤(7623/250:ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤23244/25),Real.sqrt_nonneg (23244/25:ℝ)]
  have hc := mul_le_mul h0 h1 (show 0≤planarC1 from Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤0.439510742)
  have hm := mul_le_mul hc hr (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤0.439510742*0.3030651876)
  exact hm.trans (by norm_num)

/-- The literal outward polynomial in AN (3.3), with no numerical premise. -/
theorem old_signed_derivative_shape_polynomial {rho : ℝ} (hrho : 0≤rho) :
    oldSignedDerivativeShape rho≤(503/200:ℝ)*rho+(2031/500:ℝ)*rho^2 := by
  have hlin : (2/Real.pi)*Real.sqrt (78/5:ℝ)≤(503/200:ℝ) :=
    old_signed_derivative_linear_cap.le.trans (by norm_num)
  have h0 := mul_le_mul_of_nonneg_right hlin hrho
  have h1 := mul_le_mul_of_nonneg_right old_signed_derivative_quadratic_cap (sq_nonneg rho)
  have hh := add_le_add h0 h1
  convert hh using 1
  dsimp [oldSignedDerivativeShape]
  ring

/-- Exact extraction of the physical amplitude and source side/length
ratio from the proved row coefficient. -/
theorem old_signed_derivative_kappa_shape (r b L : ℝ) (hL : 0<L) :
    oldSignedDerivativeKappa r b L=oldSignedDerivativeShape (r/L)*|b| := by
  have h1 : (78/5:ℝ)*b^2/L^2=(78/5:ℝ)*(b/L)^2 := by ring
  have h2 : (23244/25:ℝ)*b^2/L^4=(23244/25:ℝ)*(b/L^2)^2 := by
    field_simp
  unfold oldSignedDerivativeKappa
  rw [h1,h2,Real.sqrt_mul (by norm_num : (0:ℝ)≤78/5),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤23244/25),Real.sqrt_sq_eq_abs,
    Real.sqrt_sq_eq_abs,abs_div,abs_div,abs_of_pos hL,abs_of_nonneg (sq_nonneg L)]
  unfold oldSignedDerivativeShape
  field_simp

end
end ASDExplicitGamma.Native
