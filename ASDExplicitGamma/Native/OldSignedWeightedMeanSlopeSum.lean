module

public import ASDExplicitGamma.Native.OldSignedWeightedMeanMajorant

/-! Complete inverse-weighted OLD source-mean slope, with no finite cutoff. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Scalar Inverse Variational Cold Algsuperdiff.Section3
noncomputable section

/-- The genuine positive source coefficient is nonnegative at every depth. -/
theorem old_signed_mean_source_cap_nonneg (M : ABKModel 2) (h : ℝ) (n : ℤ) (j : ℕ) :
    0≤oldSignedMeanSourceCap M h n (5+j) := by
  have hg := M.shellPrefix.gamma_pos.le
  have hp := old_signed_full64_depth_parameters (n-((5+j:ℕ):ℤ)) j
  dsimp only at hp
  have hmu := (pureFlux_covariance_mu_lower (pureFluxCovarianceA 0 (6+j-1))
    (pureFluxCovarianceB 0 (6+j-1))).1
  dsimp only [oldSignedMeanSourceCap]
  rw [show 5+j+1=6+j by omega,hp.1,hp.2.1]
  dsimp only [lemmaVH2kn,lemmaVH2R1,lemmaVH2C1,lemmaVH2C2,
    rawTraceOldFrameP20LocalClock,oldSignedP20Full64Cap]
  positivity

/-- The whole weak-weighted first-moment slope is at most 0.018 theta.
The complete inverse-bank baseline is included in the normalization. -/
theorem old_signed_weighted_mean_source_slope_sum
    (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      oldSignedMeanSourceCap M h n (5+j)) ∧
    (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)*
      (∑' j : ℕ,inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
        oldSignedMeanSourceCap M h n (5+j)) ≤ (9/500)*theta M := by
  have hθ : 0≤theta M := (cold_theta_pos M).le
  have hm := old_signed_weighted_mean_majorant_hasSum.summable
  have hmn : 0≤∑' j,oldSignedWeightedMeanSlopeMajorant j := by
    apply tsum_nonneg
    intro j
    dsimp [oldSignedWeightedMeanSlopeMajorant]
    positivity
  have hn (j : ℕ) : 0≤ inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      oldSignedMeanSourceCap M h n (5+j) :=
    mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (by unfold bankDepthFrame; positivity)) (old_signed_mean_source_cap_nonneg M h n j)
  have hu := Summable.of_nonneg_of_le hn
    (old_signed_weighted_mean_source_majorant M h n hg hstate) (hm.mul_left (theta M))
  have hsum := hu.tsum_le_tsum (old_signed_weighted_mean_source_majorant M h n hg hstate)
    (hm.mul_left (theta M))
  rw [tsum_mul_left] at hsum
  have hdiscount : 1-inverseHistoryDiscount^2≤423/1000 := by
    linarith only [old_signed_weak_discount_caps.1]
  have hdiscount0 : 0≤1-inverseHistoryDiscount^2 := by
    have hh := old_signed_weak_discount_caps.2
    linarith only [hh]
  have hmajor : (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)*
      (∑' j,oldSignedWeightedMeanSlopeMajorant j) ≤ 9/500 := by
    calc
      _ ≤ (423/1000)*(3683/2500:ℝ)*(∑' j,oldSignedWeightedMeanSlopeMajorant j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdiscount (by norm_num)) hmn
      _ ≤ _ := by
        rw [old_signed_weighted_mean_majorant_hasSum.tsum_eq]
        simpa only [mul_assoc] using old_signed_weighted_mean_slope_numeric
  refine ⟨hu,?_⟩
  have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg hdiscount0 (by norm_num : (0:ℝ)≤3683/2500))
  have hlast := mul_le_mul_of_nonneg_right hmajor hθ
  calc
    _ ≤ (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)*
        (theta M*∑' j,oldSignedWeightedMeanSlopeMajorant j) := hh
    _ ≤ _ := by convert hlast using 1; ring

end
end ASDExplicitGamma.Native
