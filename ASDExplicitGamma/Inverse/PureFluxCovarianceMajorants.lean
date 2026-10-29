module

public import ASDExplicitGamma.Inverse.PureFluxCovarianceRows

/-! All-shell positive covariance majorants, with exactly the producer's tail powers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The source upward row envelope (ar+BA)*rho+CA*rho^2. -/
def pureFluxCovarianceMajorant (q i : ℕ) : ℝ :=
  ((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))*pureFluxCovarianceRho q i+
    (Numerics.Inverse.invCov0CA:ℝ)*(pureFluxCovarianceRho q i)^2

/-- Exactly the rho^2,rho^3,rho^4 polynomial used in the complete numeric tail. -/
def pureFluxCovarianceMuMajorant (q i : ℕ) : ℝ :=
  (233/100:ℝ)*
    ((((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))^2)*(pureFluxCovarianceRho q i)^2+
    2*((Numerics.Inverse.invCov0Ar:ℝ)+(Numerics.Inverse.invCov0BA:ℝ))*(Numerics.Inverse.invCov0CA:ℝ)*
      (pureFluxCovarianceRho q i)^3+
    (Numerics.Inverse.invCov0CA:ℝ)^2*(pureFluxCovarianceRho q i)^4)

theorem pureFlux_covariance_numeric_coefficients_nonneg :
    (0:ℝ) ≤ (Numerics.Inverse.invCov0Ar:ℝ) ∧
    (0:ℝ) ≤ (Numerics.Inverse.invCov0BA:ℝ) ∧
    (0:ℝ) ≤ (Numerics.Inverse.invCov0CA:ℝ) := by
  have hh := pureFlux_covariance_coefficient_caps
  exact ⟨(show 0 ≤ pureFluxCovarianceAr by unfold pureFluxCovarianceAr; positivity).trans hh.1,
    (show 0 ≤ pureFluxCovarianceBA by unfold pureFluxCovarianceBA; positivity).trans hh.2.1,
    (show 0 ≤ pureFluxCovarianceCA by unfold pureFluxCovarianceCA; positivity).trans hh.2.2.2.1⟩

/-- The exact covariance row is bounded on every shell, including the full
infinite tail, by the same literal upward row used by the producer. -/
theorem pureFlux_covariance_A_le_majorant (q i : ℕ) :
    pureFluxCovarianceA q i ≤ pureFluxCovarianceMajorant q i := by
  have hρ := (pureFlux_covariance_rho_pos q i).le
  have hδ := pureFlux_covariance_delta_bounds q i
  have hc := pureFlux_covariance_coefficient_caps
  have hn := pureFlux_covariance_numeric_coefficients_nonneg
  have h1 := mul_le_mul_of_nonneg_right hc.1 hρ
  have h2 := (mul_le_mul_of_nonneg_right hc.2.1 hδ.1).trans
    (mul_le_mul_of_nonneg_left hδ.2 hn.2.1)
  have h3 := (mul_le_mul_of_nonneg_right hc.2.2.2.1 (sq_nonneg (pureFluxCovarianceDelta q i))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.1 hδ.2 2) hn.2.2)
  unfold pureFluxCovarianceA pureFluxCovarianceMajorant
  nlinarith only [h1,h2,h3]

/-- The actual positive feedback coefficient obeys the complete producer
polynomial majorant, without replacing its infinite tail by a finite scan. -/
theorem pureFlux_covariance_mu_le_majorant (q i : ℕ) :
    pureFluxCovarianceMu (pureFluxCovarianceA q i) (pureFluxCovarianceB q i) ≤
      pureFluxCovarianceMuMajorant q i := by
  have hrows := pureFlux_covariance_rows_order q i
  have hA : 0 ≤ pureFluxCovarianceA q i := hrows.1.trans hrows.2
  have hh := (pureFlux_covariance_rows_mu_tail q i).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA (pureFlux_covariance_A_le_majorant q i) 2)
      (by norm_num : (0:ℝ) ≤ 233/100))
  apply hh.trans_eq
  unfold pureFluxCovarianceMajorant pureFluxCovarianceMuMajorant
  ring

end
end ASDExplicitGamma.Inverse
