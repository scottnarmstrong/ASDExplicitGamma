module

public import ASDExplicitGamma.Native.OldSignedMaxHistoryAffine
public import ASDExplicitGamma.Native.OldSignedWeightedMeanRatios

/-! Native strong20 pays the complete unbounded initial-mean tail. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Cold Variational Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The mean is paid by its finite twentieth moment, with finiteness supplied
by the actual native state before taking a real seminorm. -/
theorem old_signed_initial_mean_le_L20 (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hstate : nativeInductionState M h n) (r : ℕ) :
    (∫ ω,cutoffTraceDefect M n (n-(r:ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      lpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hf := cold_native_fine_memLp hstate.2.1 r
  have hh := ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := cutoffTraceDefect M n (n-(r:ℤ)))
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (by norm_num : (1:ℝ≥0∞)≤20))
  change lpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 1 _ ≤ lpNorm _ 20 _ at hh
  rw [lpNorm_one_eq_integral_norm hf.aestronglyMeasurable] at hh
  simpa only [Real.norm_of_nonneg (cutoffTraceDefect_nonneg M n (n-(r:ℤ)) _)] using hh

/-- Elementary lower normalization and lower beta gates for the tail. -/
theorem old_signed_initial_history_tail_gates :
    (6/25:ℝ)≤1-inverseHistoryDiscount ∧ (21/25:ℝ)≤coldHistoryBeta := by
  have ha : inverseHistoryDiscount^4=(1/3:ℝ) := by
    unfold inverseHistoryDiscount
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    norm_num [Real.rpow_neg,Real.rpow_natCast]
  have hal : inverseHistoryDiscount≤19/25 := by
    apply (pow_le_pow_iff_left₀ inverse_history_discount_range.1.le
      (by norm_num : (0:ℝ)≤19/25) (by norm_num : (4:ℕ)≠0)).mp
    rw [ha]
    norm_num
  have hb : coldHistoryBeta^20=(1/27:ℝ) := by
    rw [cold_native_beta_power]
    norm_num [Real.rpow_neg,Real.rpow_natCast]
  refine ⟨by linarith only [hal],?_⟩
  apply (pow_le_pow_iff_left₀ (by norm_num : (0:ℝ)≤21/25) coldHistoryBeta_pos.le
    (by norm_num : (20:ℕ)≠0)).mp
  rw [hb]
  norm_num

/-- A coarse whole-series bound suffices once the tail carries geometric
smallness; the exact initial strong input remains theta-scaled. -/
theorem old_signed_initial_mean_strong_profile (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let T := fun j : ℕ => ∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure
    Summable (fun j => coldHistoryBeta^j*T j) ∧
      (∑' j,coldHistoryBeta^j*T j)≤10*theta M := by
  intro T
  let B := fun j : ℕ => lpNorm (cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)))
    20 (Cutoff.cutoffSampleLaw M).toMeasure
  have hθ := (cold_theta_pos M).le
  have hs := old_signed_shifted_strong_profile M n 5 _
    (mul_nonneg (by norm_num : (0:ℝ)≤2379/2500) hθ) hstate.2.1
  have hnorm0 : 0≤∑' j,coldHistoryBeta^j*B j :=
    tsum_nonneg (fun j => mul_nonneg (pow_nonneg coldHistoryBeta_pos.le j) lpNorm_nonneg)
  have hh := mul_le_mul_of_nonneg_right old_signed_initial_history_tail_gates.1 hnorm0
  have hinit := mul_le_mul_of_nonneg_right old_signed_initial_history_rational hθ
  have hnormsum : (∑' j,coldHistoryBeta^j*B j)≤10*theta M := by
    dsimp only [B] at *
    nlinarith only [hh,hs.2,hinit,hθ]
  have hcap (j : ℕ) : coldHistoryBeta^j*T j≤coldHistoryBeta^j*B j :=
    mul_le_mul_of_nonneg_left (old_signed_initial_mean_le_L20 M h n hstate (5+j))
      (pow_nonneg coldHistoryBeta_pos.le j)
  have hT0 (j : ℕ) : 0≤coldHistoryBeta^j*T j := mul_nonneg
    (pow_nonneg coldHistoryBeta_pos.le j) (integral_nonneg (cutoffTraceDefect_nonneg _ _ _))
  have hsum := Summable.of_nonneg_of_le hT0 hcap hs.1
  exact ⟨hsum,(hsum.tsum_le_tsum hcap hs.1).trans hnormsum⟩

end
end ASDExplicitGamma.Native
