module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBandGenerator
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! Coefficient clocks for the actual simultaneous-band inverse generator. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The actual fresh-shell covariance row is at most one under its
literal parent/source-mesh ratios. -/
theorem parent_boundary_covariance_A_le_one (q i : ℕ)
    (hρ : pureFluxCovarianceRho q i ≤ (3 : ℝ)⁻¹)
    (hδ : pureFluxCovarianceDelta q i ≤ (243 : ℝ)⁻¹) :
    pureFluxCovarianceA q i ≤ 1 := by
  have hAr : pureFluxCovarianceAr ≤ 14 / 5 := by
    unfold pureFluxCovarianceAr
    nlinarith [Real.sq_sqrt (show 0 ≤ (78 / 5 : ℝ) / 2 by norm_num)]
  have hBA : pureFluxCovarianceBA ≤ 81 / 10 := by
    unfold pureFluxCovarianceBA
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * (78 / 5 : ℝ) by norm_num)]
  have hCA : pureFluxCovarianceCA ≤ 62 / 5 := by
    unfold pureFluxCovarianceCA
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * ((3432 / 5 : ℝ) + (78 / 5 : ℝ)^2) by norm_num)]
  have hρ0 := pureFlux_covariance_rho_pos q i
  have hδ0 := pureFlux_covariance_delta_bounds q i
  have hδ2 : (pureFluxCovarianceDelta q i)^2 ≤ (243 : ℝ)⁻¹ ^ 2 :=
    (sq_le_sq₀ hδ0.1 (by positivity)).2 hδ
  have h1 : pureFluxCovarianceAr * pureFluxCovarianceRho q i ≤
      (14 / 5 : ℝ) * (3 : ℝ)⁻¹ :=
    mul_le_mul hAr hρ hρ0.le (by norm_num)
  have h2 : pureFluxCovarianceBA * pureFluxCovarianceDelta q i ≤
      (81 / 10 : ℝ) * (243 : ℝ)⁻¹ :=
    mul_le_mul hBA hδ hδ0.1 (by norm_num)
  have h3 : pureFluxCovarianceCA * (pureFluxCovarianceDelta q i)^2 ≤
      (62 / 5 : ℝ) * (243 : ℝ)⁻¹ ^ 2 :=
    mul_le_mul hCA hδ2 (sq_nonneg _) (by norm_num)
  unfold pureFluxCovarianceA
  norm_num at h1 h2 h3 ⊢
  nlinarith


/-- Both actual fresh covariance rows fit the unit square. -/
theorem parent_boundary_fresh_covariance_caps (i : ℕ) :
    pureFluxCovarianceA 0 i≤1 ∧ pureFluxCovarianceB 0 i≤1 := by
  have hrho : pureFluxCovarianceRho 0 i≤(3:ℝ)⁻¹ := by
    unfold pureFluxCovarianceRho
    have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/3)
      (by norm_num : (1/3:ℝ)≤1) (show 1≤0+i+1 by omega)
    simpa only [pow_one,one_div] using hp
  have hdelta : pureFluxCovarianceDelta 0 i≤(243:ℝ)⁻¹ := by
    simpa only [pureFluxCovarianceDelta,one_div] using
      (min_le_left (1/243:ℝ) (pureFluxCovarianceRho 0 i))
  have ha := parent_boundary_covariance_A_le_one 0 i hrho hdelta
  exact ⟨ha,(pureFlux_covariance_rows_order 0 i).2.trans ha⟩

/-- The literal inverse-loss coefficient is at most mu(1,1) times the
actual full fresh variance; no variance is replaced by the smaller Y clock. -/
theorem parent_boundary_inverse_band_clock_le_variance (M : ABKModel 2) (h : ℝ)
    (n : ℤ) (height : ℕ) :
    parentBoundaryBandInverseClock M h n height≤
      pureFluxCovarianceMu 1 1*parentBoundaryBandVariance M h n height := by
  unfold parentBoundaryBandInverseClock parentBoundaryBandVariance
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have ho := pureFlux_covariance_rows_order 0 i.val
  have hc := parent_boundary_fresh_covariance_caps i.val
  have hm := pureFlux_covariance_mu_mono (pureFluxCovarianceB 0 i.val)
    (pureFluxCovarianceA 0 i.val) 1 1 ho.1 (ho.1.trans ho.2) hc.2 hc.1
  have hh := mul_le_mul_of_nonneg_left hm
    (div_nonneg (sq_nonneg (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))))
      (sq_nonneg (Annealed.sigmaBar M n:ℝ)))
  simpa only [div_pow,mul_comm] using hh

/-- A small rational enclosure for the exact two-channel unit covariance
root, with its square-root comparison proved by a rational certificate. -/
theorem parent_boundary_inverse_unit_root_cap : pureFluxCovarianceMu 1 1≤232/125 :=
  pureFlux_covariance_mu_le_of_certificate 1 1 (232/125) (by norm_num) (by norm_num)

end
end ASDExplicitGamma.Native
