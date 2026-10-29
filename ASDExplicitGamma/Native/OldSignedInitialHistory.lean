module

public import ASDExplicitGamma.Native.OldSignedMaxTraceLaw
public import ASDExplicitGamma.Cold.NativeStrongHistory

/-! The exact shifted strong-history input to the OLD q1 panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- Shifting the actual completed strong history costs exactly beta to the
negative shift. The theta factor is retained in the input cap S. -/
theorem old_signed_shifted_strong_profile (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (S : ℝ) (hS : 0 ≤ S) (hstrong : strong20 M n ≤ ENNReal.ofReal S) :
    Summable (fun j : ℕ => coldHistoryBeta^j *
      lpNorm (cutoffTraceDefect M n (n-((r+j:ℕ):ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j *
      lpNorm (cutoffTraceDefect M n (n-((r+j:ℕ):ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure) ≤ (coldHistoryBeta^r)⁻¹*S := by
  let B := fun j : ℕ => lpNorm (cutoffTraceDefect M n (n-((r+j:ℕ):ℤ)))
    20 (Cutoff.cutoffSampleLaw M).toMeasure
  have hs := cold_native_strong_sum hS hstrong
  have hshift := hs.1.comp_injective (show Function.Injective (fun j : ℕ => j+r) from
    fun _ _ hh => Nat.add_right_cancel hh)
  have hterm (j : ℕ) : coldNativeStrongRealTerm M n (j+r) =
      ((1-inverseHistoryDiscount)*coldHistoryBeta^r)*(coldHistoryBeta^j*B j) := by
    unfold coldNativeStrongRealTerm
    rw [show n-((j+r:ℕ):ℤ)=n-((r+j:ℕ):ℤ) by omega,
      pow_add]
    change (1-inverseHistoryDiscount)*(coldHistoryBeta^j*coldHistoryBeta^r)*B j = _
    ring
  have hc : 0 < (1-inverseHistoryDiscount)*coldHistoryBeta^r :=
    mul_pos (sub_pos.mpr inverse_history_discount_range.2) (pow_pos coldHistoryBeta_pos r)
  have hsum : Summable (fun j : ℕ => coldHistoryBeta^j*B j) := by
    simp only [Function.comp_def] at hshift
    simp_rw [hterm] at hshift
    exact (summable_mul_left_iff hc.ne').mp hshift
  refine ⟨hsum,?_⟩
  have hprefix : 0 ≤ ∑ j ∈ Finset.range r,coldNativeStrongRealTerm M n j := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr coldHistoryAlpha_le_one)
      (pow_nonneg coldHistoryBeta_pos.le j)) lpNorm_nonneg
  have htail : (∑' j : ℕ,coldNativeStrongRealTerm M n (j+r)) ≤ S := by
    have he := hs.1.sum_add_tsum_nat_add r
    linarith only [he,hprefix,hs.2]
  simp_rw [hterm] at htail
  rw [tsum_mul_left] at htail
  have hb := pow_pos coldHistoryBeta_pos r
  have hh := mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr hb.le)
  calc
    (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j*B j) =
        (coldHistoryBeta^r)⁻¹*(((1-inverseHistoryDiscount)*coldHistoryBeta^r)*
          (∑' j : ℕ,coldHistoryBeta^j*B j)) := by
      field_simp
    _ ≤ _ := hh

/-- The q1 initial profile follows from the genuine earlier native state,
retaining the precise strong-coordinate coefficient and theta scaling. -/
theorem old_signed_initial_q1_profile (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j *
      lpNorm (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) 0) 20
        (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (coldHistoryBeta^5)⁻¹*((2379/2500:ℝ)*theta M) := by
  simp_rw [Main.main_rawDepthFourLoadTrace_lpNorm_twenty_zero_eq_cutoff]
  exact (old_signed_shifted_strong_profile M n 5 _
    (mul_nonneg (by norm_num) (cold_theta_pos M).le) hstate.2.1).2

end
end ASDExplicitGamma.Native
