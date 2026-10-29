module

public import ASDExplicitGamma.Native.ParentHistoryEndpoint
public import ASDExplicitGamma.Native.OldSignedWeightedMeanRatios

/-! Coarse endpoint clocks used only to pay theta-scaled marginal reserves. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- A simple eighth-power rational certificate for the geometric margins. -/
theorem parent_weak_three_neg_eighth_le : (3:ℝ)^(-(1/8:ℝ)) ≤ 9/10 := by
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0:ℝ)≤9/10) (by decide : (8:ℕ)≠0)).mp
  rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  norm_num

/-- All finite source covariance clocks of these sixteen bands are at
most one; no actual probability estimate is assumed. -/
theorem parent_weak_source_clock_caps (height r p : ℕ) (hh : height ≤ 16) :
    parentBoundaryCommonSourceVariance gammaZero height ≤ 1 ∧
      parentBoundaryCommonSourceSpatialClock gammaZero height r p ≤ 1 := by
  have hshell (i : Fin height) : nativeSourceShellClock gammaZero (i.val+1) ≤ (27/2:ℝ)*gammaZero := by
    have hi : ((i.val+1:ℕ):ℝ) ≤ 16 := by exact_mod_cast (show i.val+1≤16 by omega)
    have he : 2*gammaZero*((i.val+1:ℕ):ℝ) ≤ 1 := by norm_num [gammaZero] at *; linarith only [hi]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) he
    unfold nativeSourceShellClock
    exact (mul_le_mul_of_nonneg_left hp (by norm_num [gammaZero] : (0:ℝ)≤(9/2)*gammaZero)).trans_eq (by norm_num; ring)
  have hv : parentBoundaryCommonSourceVariance gammaZero height ≤ 1 := by
    unfold parentBoundaryCommonSourceVariance
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hshell i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    have hhR : (height:ℝ) ≤ 16 := by exact_mod_cast hh
    exact hs.trans ((mul_le_mul_of_nonneg_right hhR (by norm_num [gammaZero] : (0:ℝ)≤(27/2)*gammaZero)).trans (by norm_num [gammaZero]))
  refine ⟨hv,?_⟩
  apply le_trans ?_ hv
  unfold parentBoundaryCommonSourceSpatialClock parentBoundaryCommonSourceVariance
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)≤1))
    (by unfold nativeSourceShellClock; norm_num [gammaZero]; positivity)).trans_eq (mul_one _)

/-- Coarse raw response factors, uniform on the protected source gap. -/
theorem parent_weak_source_raw_caps (height r : ℕ) (hh : height ≤ 16) (hr : r ≤ 5) :
    parentBoundaryCommonRawFactor gammaZero height r ≤ 12 ∧
      parentBoundaryCommonRawBase gammaZero height r ≤ 10000 ∧ 32474*gammaZero ≤ 12 := by
  have hhR : (height:ℝ)≤16 := by exact_mod_cast hh
  have hrR : (r:ℝ)≤5 := by exact_mod_cast hr
  have he : (2*(height:ℝ)+4*(r:ℝ)+4)*gammaZero ≤ 1 := by
    norm_num [gammaZero]
    linarith only [hhR,hrR]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) he
  refine ⟨?_,?_,by norm_num [gammaZero]⟩
  · unfold parentBoundaryCommonRawFactor
    exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans_eq (by norm_num)
  · unfold parentBoundaryCommonRawBase gammaZero
    norm_num
    linarith only [hhR,hrR]

/-- A uniform rational margin for every source history degree. -/
theorem parent_weak_common_ratio_le (growth : ℝ) (hg : growth ≤ 8) (i : Fin 5) :
    parentBoundaryCommonHistoryRatio gammaZero growth i ≤ 9/10 := by
  have hbase0 : 0 ≤ coldHistoryBeta*(3:ℝ)^(growth*gammaZero) := mul_nonneg coldHistoryBeta_pos.le (Real.rpow_nonneg (by norm_num) _)
  have hb : coldHistoryBeta=(3:ℝ)^(-(3/20:ℝ)) := by simpa using cold_native_beta_power 1
  calc
    _ ≤ coldHistoryBeta*(3:ℝ)^(growth*gammaZero) := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num : (0:ℝ)≤1/3) (by norm_num : (1/3:ℝ)≤1)) hbase0).trans_eq (mul_one _)
    _ = (3:ℝ)^(-(3/20:ℝ)+growth*gammaZero) := by rw [hb,Real.rpow_add (by norm_num : (0:ℝ)<3)]
    _ ≤ (3:ℝ)^(-(1/8:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num [gammaZero]; linarith only [hg])
    _ ≤ _ := parent_weak_three_neg_eighth_le

end
end ASDExplicitGamma.Native
