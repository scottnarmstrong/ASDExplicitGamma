module

public import ASDExplicitGamma.Native.ParentBoundaryCommonDepthTheta

/-! Proportional endpoint normalization of the actual complete centered history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The exact complete source delta retains a full theta factor, without
rerounding any numerical input or moving a reserve into theta. -/
theorem parent_boundary_common_source_delta_theta
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height r : ℕ) :
    parentBoundaryCommonSourceDelta M.gamma height r ≤ theta M*parentBoundaryCommonSourceDelta gammaZero height r := by
  have hgamma := parent_boundary_common_source_delta_sum M.gamma M.shellPrefix.gamma_pos.le hg height r
  have hzero := parent_boundary_common_source_delta_sum gammaZero (by norm_num [gammaZero]) le_rfl height r
  have hle (j : ℕ) : coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift M.gamma height r j ≤
      theta M*(coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift gammaZero height r j) :=
    (mul_le_mul_of_nonneg_left (parent_boundary_common_source_depth_theta M hg height r j)
      (pow_nonneg coldHistoryBeta_pos.le _)).trans_eq (by ring)
  have hh := hgamma.1.tsum_le_tsum hle (hzero.1.mul_left (theta M))
  rw [tsum_mul_left] at hh
  have ha : 0 ≤ 1-inverseHistoryDiscount := sub_nonneg.mpr inverse_history_discount_range.2.le
  calc
    _ = (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift M.gamma height r j) := hgamma.2.symm
    _ ≤ (1-inverseHistoryDiscount)*(theta M*(∑' j : ℕ,coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift gammaZero height r j)) :=
      mul_le_mul_of_nonneg_left hh ha
    _ = _ := by rw [←hzero.2]; ring

/-- The native shifted strong history has exactly the source H0 power. -/
theorem parent_boundary_common_initial_history_power (r : ℕ) :
    (coldHistoryBeta^r)⁻¹=(3:ℝ)^((3:ℝ)*(r:ℝ)/20) := by
  rw [cold_native_beta_power,←Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

/-- The actual complete centered history has the source endpoint envelope
with one exact theta factor. This is an L20 estimate on the genuine cutoff
sample law, with all descendants and their common-noise correlations paid. -/
theorem parent_boundary_common_centered_history_endpoint_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (parentBoundaryCommonCenteredMaxHistory M P n height t) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*((3:ℝ)^((3:ℝ)*(r:ℝ)/20)+t*parentBoundaryCommonSourceDelta gammaZero height r)) := by
  have hh := parent_boundary_common_centered_history_delta_L20 M h hM hg P n r hr hP hstate height hheight hpast t ht0 ht1
  have hd := parent_boundary_common_source_delta_theta M hg height r
  have hi : (coldHistoryBeta^r)⁻¹*((2379/2500:ℝ)*theta M) ≤ theta M*(coldHistoryBeta^r)⁻¹ :=
    (mul_le_mul_of_nonneg_left
      (by nlinarith only [(cold_theta_pos M).le] : (2379/2500:ℝ)*theta M ≤ theta M)
      (inv_nonneg.mpr (pow_nonneg coldHistoryBeta_pos.le _))).trans_eq (mul_comm _ _)
  have hsum := add_le_add hi (mul_le_mul_of_nonneg_left hd ht0)
  apply hh.trans (ENNReal.ofReal_le_ofReal (hsum.trans_eq ?_))
  rw [parent_boundary_common_initial_history_power]
  ring

end
end ASDExplicitGamma.Native
