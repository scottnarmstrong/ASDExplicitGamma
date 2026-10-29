module

public import ASDExplicitGamma.Native.OldSignedInitialMeanStrong

/-! Entire initial-mean tail paid by the genuine earlier strong20 coordinate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Relative to the strong-history weight, the initial weak weight decays
at least geometrically with ratio 0.7. -/
theorem old_signed_initial_weight_beta (M : ABKModel 2) (hg : M.gamma≤gammaZero) (j : ℕ) :
    inverseHistoryDiscount^(2*j)*bankDepthFrame M j ≤ (7/10:ℝ)^j*coldHistoryBeta^j := by
  have hb : (289/500:ℝ)*(1001/1000)≤(7/10)*coldHistoryBeta := by
    linarith only [old_signed_initial_history_tail_gates.2]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(289/500)*(1001/1000)) hb j
  rw [mul_pow (7/10:ℝ) coldHistoryBeta] at hp
  exact (old_signed_weighted_mean_depth_weight M hg j).trans hp

/-- Every depth beyond the finite initial-law prefix is retained in the
series and paid by strong20, with its theta factor and no raw tail cutoff. -/
theorem old_signed_initial_mean_tail (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hg : M.gamma≤gammaZero) (hstate : nativeInductionState M h n) :
    let T := fun j : ℕ => ∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*(j+65))*bankDepthFrame M (j+65)*T (j+65)) ∧
    (∑' j : ℕ,inverseHistoryDiscount^(2*(j+65))*bankDepthFrame M (j+65)*T (j+65)) ≤
      (1/1000)*theta M := by
  intro T
  let B := fun j : ℕ => coldHistoryBeta^j*T j
  have hs := old_signed_initial_mean_strong_profile M h n hstate
  have hT0 (j : ℕ) : 0≤T j := integral_nonneg (cutoffTraceDefect_nonneg _ _ _)
  have hB0 (j : ℕ) : 0≤B j := mul_nonneg (pow_nonneg coldHistoryBeta_pos.le _) (hT0 j)
  have hshift : Summable (fun j : ℕ => B (j+65)) :=
    hs.1.comp_injective (show Function.Injective (fun j : ℕ => j+65) from
      fun _ _ hh => Nat.add_right_cancel hh)
  have hshiftcap : (∑' j : ℕ,B (j+65))≤10*theta M := by
    have hh := hs.1.sum_add_tsum_nat_add 65
    have hp : 0≤∑ j ∈ Finset.range 65,B j := Finset.sum_nonneg (fun j _ => hB0 j)
    change (∑ j ∈ Finset.range 65,B j)+(∑' j : ℕ,B (j+65))=(∑' j : ℕ,B j) at hh
    linarith only [hh,hp,hs.2]
  have hcap (j : ℕ) : inverseHistoryDiscount^(2*(j+65))*bankDepthFrame M (j+65)*T (j+65) ≤
      (7/10:ℝ)^65*B (j+65) := by
    have hw := mul_le_mul_of_nonneg_right (old_signed_initial_weight_beta M hg (j+65)) (hT0 (j+65))
    have hp : (7/10:ℝ)^(j+65)≤(7/10:ℝ)^65 := by
      rw [pow_add]
      have hh := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (by norm_num : (0:ℝ)≤7/10) (by norm_num : (7/10:ℝ)≤1) : (7/10:ℝ)^j≤1)
        (by positivity : (0:ℝ)≤(7/10)^65)
      simpa only [one_mul] using hh
    have hh := mul_le_mul_of_nonneg_right hp (hB0 (j+65))
    exact hw.trans (by simpa only [B,mul_assoc] using hh)
  have hn (j : ℕ) : 0 ≤ inverseHistoryDiscount^(2*(j+65))*bankDepthFrame M (j+65)*T (j+65) :=
    mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (by unfold bankDepthFrame; positivity)) (hT0 (j+65))
  have hu := Summable.of_nonneg_of_le hn hcap (hshift.mul_left ((7/10:ℝ)^65))
  have hh := hu.tsum_le_tsum hcap (hshift.mul_left ((7/10:ℝ)^65))
  rw [tsum_mul_left] at hh
  refine ⟨hu,hh.trans ?_⟩
  have hbound := mul_le_mul_of_nonneg_left hshiftcap (by positivity : (0:ℝ)≤(7/10)^65)
  have hnum : (7/10:ℝ)^65*10≤1/1000 := by norm_num
  have hlast := mul_le_mul_of_nonneg_right hnum (cold_theta_pos M).le
  exact hbound.trans (by simpa only [mul_assoc] using hlast)

end
end ASDExplicitGamma.Native
