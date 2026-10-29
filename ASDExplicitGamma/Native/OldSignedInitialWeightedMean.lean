module

public import ASDExplicitGamma.Native.OldSignedInitialMeanPrefix

/-! Complete initial inverse-weighted mean budget from generic rows and strong20. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The initial weak-mean baseline is at most 0.23 theta, including every
depth. All inputs are generic producers or earlier native state coordinates. -/
theorem old_signed_initial_weighted_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n) :
    let T := fun j : ℕ => ∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*T j) ∧
    (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)*
      (∑' j : ℕ,inverseHistoryDiscount^(2*j)*bankDepthFrame M j*T j) ≤ (23/100)*theta M := by
  intro T
  let F := fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*T j
  let G : ℝ := (7/50)/(1-29/50)+(3/500)*(29/50)/(1-29/50)^2
  have hθ := (cold_theta_pos M).le
  have hs := old_signed_initial_mean_strong_profile M h n hstate
  have hT0 (j : ℕ) : 0≤T j := integral_nonneg (cutoffTraceDefect_nonneg _ _ _)
  have hF0 (j : ℕ) : 0≤F j := mul_nonneg
    (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (by unfold bankDepthFrame; positivity)) (hT0 j)
  have hcap (j : ℕ) : F j≤coldHistoryBeta^j*T j := by
    have hh := mul_le_mul_of_nonneg_right (old_signed_initial_weight_beta M hg j) (hT0 j)
    have hp : (7/10:ℝ)^j≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hh' := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (pow_nonneg coldHistoryBeta_pos.le j) (hT0 j))
    exact hh.trans (by simpa only [mul_assoc,one_mul] using hh')
  have hu : Summable F := Summable.of_nonneg_of_le hF0 hcap hs.1
  have hhead := old_signed_initial_mean_prefix_sum M h hM hg n hpast
  have htail := (old_signed_initial_mean_tail M h n hg hstate).2
  have heq := hu.sum_add_tsum_nat_add 65
  have htotal : (∑' j,F j)≤theta M*(G+1/1000) := by
    change (∑ j ∈ Finset.range 65,F j)≤theta M*G at hhead
    change (∑' j : ℕ,F (j+65))≤(1/1000)*theta M at htail
    rw [←heq]
    exact (add_le_add hhead htail).trans_eq (by ring)
  have hcoeff : (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)≤(423/1000)*(3683/2500) := by
    have hh : 1-inverseHistoryDiscount^2≤423/1000 := by
      linarith only [old_signed_weak_discount_caps.1]
    exact mul_le_mul_of_nonneg_right hh (by norm_num)
  have hh := mul_le_mul hcoeff htotal (tsum_nonneg hF0)
    (by norm_num : (0:ℝ)≤(423/1000)*(3683/2500))
  have hnum : (423/1000:ℝ)*(3683/2500)*(G+1/1000)≤23/100 := by norm_num [G]
  have hlast := mul_le_mul_of_nonneg_right hnum hθ
  refine ⟨hu,hh.trans ?_⟩
  convert hlast using 1
  ring

end
end ASDExplicitGamma.Native
