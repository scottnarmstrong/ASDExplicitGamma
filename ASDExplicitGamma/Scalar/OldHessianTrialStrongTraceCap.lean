module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalTraceMoments
public import ASDExplicitGamma.Cold.NativeCellTrace
public import ASDExplicitGamma.Native.OldSignedInitialMeanStrong
public import ASDExplicitGamma.Numerics.Scalar.Endpoints

/-! Sharp completed OLD source trace moments from the actual strong20
coordinate. This is the source Hsrc payment, not the raw transport envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The strong weight through source depth five retains the exact
3^(3/4) factor paid by NU-SC-H-SOURCE. -/
theorem old_hessian_strong_weight_cap (r : ℕ) (hr : r≤5) :
    (2379/2500:ℝ) ≤ coldHistoryBeta^r*(5423/2500:ℝ) := by
  have hβ : coldHistoryBeta≤1 := by
    unfold coldHistoryBeta
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hpow : coldHistoryBeta^5≤coldHistoryBeta^r :=
    pow_le_pow_of_le_one coldHistoryBeta_pos.le hβ hr
  have hi : (coldHistoryBeta^5)⁻¹=(3:ℝ)^(3/4:ℝ) := by
    rw [cold_native_beta_power]
    norm_num
    rw [←Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    norm_num
  have hc := Numerics.Scalar.source_history_cap.le
  rw [←hi] at hc
  have hc' := mul_le_mul_of_nonneg_left hc (pow_nonneg coldHistoryBeta_pos.le 5)
  rw [←mul_assoc,mul_inv_cancel₀ (pow_pos coldHistoryBeta_pos 5).ne',one_mul] at hc'
  exact hc'.trans (mul_le_mul_of_nonneg_right hpow (by norm_num))

/-- The actual r0..r5 completed origin traces have finite twentieth
moments bounded by theta*Hsrc/(1-.76), from the standing native state. -/
theorem old_hessian_origin_strong_trace_cap
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r≤5) :
    eLpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*((5423/2500:ℝ)/(1-19/25))) := by
  let S := (2379/2500:ℝ)*theta M
  have hθ : 0≤theta M := (cold_theta_pos M).le
  have hs := cold_native_strong_sum (mul_nonneg (by norm_num : (0:ℝ)≤2379/2500) hθ) hstate.2.1
  have hterm : coldNativeStrongRealTerm M n r≤S :=
    (hs.1.le_tsum r (fun _ _ => mul_nonneg
      (mul_nonneg (sub_nonneg.mpr coldHistoryAlpha_le_one) (pow_nonneg coldHistoryBeta_pos.le _))
      lpNorm_nonneg)).trans hs.2
  have hweight : (6/25:ℝ)*coldHistoryBeta^r≤(1-inverseHistoryDiscount)*coldHistoryBeta^r :=
    mul_le_mul_of_nonneg_right old_signed_initial_history_tail_gates.1 (pow_nonneg coldHistoryBeta_pos.le r)
  have hnorm := mul_le_mul_of_nonneg_right hweight
    (show 0≤lpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure from lpNorm_nonneg)
  have hT : (6/25:ℝ)*coldHistoryBeta^r*
      lpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ S := hnorm.trans hterm
  have hcap : S≤coldHistoryBeta^r*(theta M*(5423/2500:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right (old_hessian_strong_weight_cap r hr) hθ
    exact hh.trans_eq (by ring)
  have hn : lpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      theta M*((5423/2500:ℝ)/(1-19/25)) := by
    have hh := hT.trans hcap
    rw [mul_assoc] at hh
    have ht := (mul_le_mul_iff_right₀ (pow_pos coldHistoryBeta_pos r)).mp
      (show coldHistoryBeta^r*((6/25:ℝ)*lpNorm (cutoffTraceDefect M n (n-(r:ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure)≤coldHistoryBeta^r*(theta M*(5423/2500:ℝ)) from
          (by convert hh using 1; ring))
    have he : theta M*((5423/2500:ℝ)/(1-19/25))=
        (theta M*(5423/2500:ℝ))/(6/25:ℝ) := by ring
    rw [he]
    exact (le_div_iff₀ (by norm_num : (0:ℝ)<6/25)).mpr ((mul_comm _ _).le.trans ht)
  have hf := cold_native_fine_memLp hstate.2.1 r
  have hh := ENNReal.ofReal_le_ofReal hn
  rw [lpNorm,ENNReal.ofReal_toReal hf.eLpNorm_ne_top] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
