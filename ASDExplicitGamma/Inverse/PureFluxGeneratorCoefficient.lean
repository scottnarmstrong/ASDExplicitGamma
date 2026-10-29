module

public import ASDExplicitGamma.Inverse.PureFluxCovarianceRows

/-! Exact conversion of the centered source-mesh radicals to the bank rows. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

private theorem pureFlux_sqrt_scaled_square (c b L : ℝ) (hc : 0 ≤ c) (hL : 0 < L) :
    Real.sqrt (c*b^2/L^2) = Real.sqrt c * |b|/L := by
  rw [Real.sqrt_div (mul_nonneg hc (sq_nonneg b)), Real.sqrt_mul hc,
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hL]

private theorem pureFlux_sqrt_scaled_fourth (c b L : ℝ) (hc : 0 ≤ c) (hL : 0 < L) :
    Real.sqrt (c*b^2/L^4) = Real.sqrt c * |b|/L^2 := by
  rw [show L^4=(L^2)^2 by ring]
  exact pureFlux_sqrt_scaled_square c b (L^2) hc (sq_pos_of_pos hL)

theorem pureFlux_centered_source_coefficient_eq (q i : ℕ) (b R r L : ℝ)
    (hL : 0 < L) (hR : R/L = pureFluxCovarianceRho q i)
    (hr : r/L = pureFluxCovarianceDelta q i) :
    Real.sqrt (b^2*((78/5:ℝ)/2)*(R/L)^2) +
      r*(36/25:ℝ)*Real.sqrt ((156/5:ℝ)*b^2/L^2) +
      r^2*(57/200:ℝ)*Real.sqrt ((46488/25:ℝ)*b^2/L^4) =
        |b| *pureFluxCovarianceA q i := by
  have hρ := (pureFlux_covariance_rho_pos q i).le
  have hbase : Real.sqrt (b^2*((78/5:ℝ)/2)*(R/L)^2) =
      |b| *Real.sqrt ((78/5:ℝ)/2)*pureFluxCovarianceRho q i := by
    rw [hR, Real.sqrt_mul (mul_nonneg (sq_nonneg b) (by norm_num)),
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hρ]
  rw [hbase, pureFlux_sqrt_scaled_square _ _ _ (by norm_num) hL,
    pureFlux_sqrt_scaled_fourth _ _ _ (by norm_num) hL]
  unfold pureFluxCovarianceA pureFluxCovarianceAr pureFluxCovarianceBA pureFluxCovarianceCA
  have hca : (2:ℝ)*((3432/5)+(78/5)^2) = 46488/25 := by norm_num
  have hba : (2:ℝ)*(78/5) = 156/5 := by norm_num
  rw [hca, hba, ← hr]
  ring

theorem pureFlux_centered_feedback_coefficient_eq (q i : ℕ) (b R r L : ℝ)
    (hL : 0 < L) (hR : R/L = pureFluxCovarianceRho q i)
    (hr : r/L = pureFluxCovarianceDelta q i) :
    Real.sqrt (b^2*((78/5:ℝ)/2)*(R/L)^2) +
      r*(36/25:ℝ)*Real.sqrt ((78/5:ℝ)*b^2/L^2) +
      r^2*(57/200:ℝ)*Real.sqrt ((23244/25:ℝ)*b^2/L^4) =
        |b| *pureFluxCovarianceB q i := by
  have hρ := (pureFlux_covariance_rho_pos q i).le
  have hbase : Real.sqrt (b^2*((78/5:ℝ)/2)*(R/L)^2) =
      |b| *Real.sqrt ((78/5:ℝ)/2)*pureFluxCovarianceRho q i := by
    rw [hR, Real.sqrt_mul (mul_nonneg (sq_nonneg b) (by norm_num)),
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hρ]
  rw [hbase, pureFlux_sqrt_scaled_square _ _ _ (by norm_num) hL,
    pureFlux_sqrt_scaled_fourth _ _ _ (by norm_num) hL]
  unfold pureFluxCovarianceB pureFluxCovarianceAr pureFluxCovarianceBB pureFluxCovarianceCB
  have hcb : (3432/5:ℝ)+(78/5)^2 = 23244/25 := by norm_num
  rw [hcb, ← hr]
  ring

/-- Scalar closure of the exact source-minus-projection generator identity. -/
theorem pureFlux_generator_source_feedback_bound (q i : ℕ)
    (c B g S C Z x y E : ℝ) (hB : 0 ≤ B)
    (hidentity : g = S + 2*C - Z) (hZ : 0 ≤ Z)
    (hsource : S ≤ B*c^2*(pureFluxCovarianceA q i)^2*x^2)
    (hfeedback : C ≤ (63/50:ℝ)*B*c^2*pureFluxCovarianceA q i*
      pureFluxCovarianceB q i*x*y)
    (hpair : x^2+y^2 ≤ B*E) :
    g ≤ c^2 * pureFluxCovarianceMu (pureFluxCovarianceA q i)
      (pureFluxCovarianceB q i) * B^2 * E := by
  have hscale : 0 ≤ B*c^2 := mul_nonneg hB (sq_nonneg c)
  have hmu := (pureFlux_covariance_mu_lower
    (pureFluxCovarianceA q i) (pureFluxCovarianceB q i)).1
  have hquad := pureFlux_covariance_quadratic_bound
    (pureFluxCovarianceA q i) (pureFluxCovarianceB q i) x y
  calc
    g ≤ B*c^2*((pureFluxCovarianceA q i)^2*x^2+
        2*(63/50:ℝ)*pureFluxCovarianceA q i*pureFluxCovarianceB q i*x*y) := by
      rw [hidentity]
      nlinarith only [hsource, hfeedback, hZ]
    _ ≤ B*c^2*(pureFluxCovarianceMu (pureFluxCovarianceA q i)
        (pureFluxCovarianceB q i)*(x^2+y^2)) :=
      mul_le_mul_of_nonneg_left hquad hscale
    _ ≤ B*c^2*(pureFluxCovarianceMu (pureFluxCovarianceA q i)
        (pureFluxCovarianceB q i)*(B*E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair hmu) hscale
    _ = _ := by ring

end
end ASDExplicitGamma.Inverse
