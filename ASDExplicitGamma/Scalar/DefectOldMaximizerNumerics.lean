module

public import ASDExplicitGamma.Inverse.ParentGapGlobalRare
public import ASDExplicitGamma.Native.OldSignedDirectionalRareReserve
public import ASDExplicitGamma.Native.OldSignedDepthSeriesArithmetic
public import ASDExplicitGamma.Native.GenericSourceShortTail
public import ASDExplicitGamma.Inverse.WeakHistoryIneq

/-! Numerical payments of the scalar correlated rare assembly. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Native ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The global rare payment of the scalar bank (`ε0 = 5·10⁻²⁴`) is below a quarter of the
`10⁻¹²θ` reserve. -/
theorem global_numeric (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      mixedBridgeOldInverseBaseline M j *
      (13 * (5 / 10 ^ 24 : ℝ) * (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j)))) ∧
    (∑' j : ℕ, (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      mixedBridgeOldInverseBaseline M j *
      (13 * (5 / 10 ^ 24 : ℝ) * (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j)))) ≤ (1 / (4 * 10 ^ 12 : ℝ)) * theta M := by
  classical
  have hαr := inverse_history_discount_range
  have hα0 : 0 ≤ inverseHistoryDiscount := hαr.1.le
  have hα1 : inverseHistoryDiscount ≤ 1 := hαr.2.le
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : (0 : ℝ) ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  have hcap : (invTraceM : ℝ) ≤ 10 ^ 6 := by exact_mod_cast invTrace_coefficient.2.1.le
  have hΔ0 : 0 ≤ 1 - inverseHistoryDiscount ^ 2 := sub_nonneg.mpr (pow_le_one₀ hα0 hα1)
  have hΔ1 : 1 - inverseHistoryDiscount ^ 2 ≤ 1 := sub_le_self _ (sq_nonneg _)
  let q : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ) + 2 * M.gamma + 6 * gammaZero + 1 / 64)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hqratio : q ≤ 9 / 10 := old_signed_depth_rare_ratio M hγ
  have hgeom := native_source_quadratic_geometric_sum (9 / 10 : ℝ) (by norm_num) (by norm_num)
  let c : ℝ := (1 - inverseHistoryDiscount ^ 2) * (3683 / 2500 : ℝ) * (13 * (5 / 10 ^ 24 : ℝ)) *
    theta M * (invTraceM : ℝ)
  have hc0 : 0 ≤ c := by
    dsimp [c]; positivity
  have hpop (j : ℕ) : 1 ≤ (9 : ℝ) ^ ((j : ℝ) / 128) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hdepthExp (j : ℕ) :
      inverseHistoryDiscount ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
        (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) ≤ (9 / 10 : ℝ) ^ j := by
    have hA0 : 0 ≤ inverseHistoryDiscount ^ (2 * j) * bankDepthFrame M j :=
      mul_nonneg (pow_nonneg hα0 _) (bankDepthFrame_pos M j).le
    have hP0 : 0 ≤ (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have h1 : inverseHistoryDiscount ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
        (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) ≤ q ^ j := by
      calc
        _ = (inverseHistoryDiscount ^ (2 * j) * bankDepthFrame M j) * 1 *
            (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) := by
          simp [bankDepthFrame]
        _ ≤ (inverseHistoryDiscount ^ (2 * j) * bankDepthFrame M j) *
            (9 : ℝ) ^ ((j : ℝ) / 128) *
            (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) := by
          have hmul := mul_le_mul_of_nonneg_left (hpop j) hA0
          exact mul_le_mul_of_nonneg_right hmul hP0
        _ = q ^ j := by
          simpa [q] using old_signed_depth_rare_weight M j
    exact h1.trans (pow_le_pow_left₀ hq0 hqratio j)
  have hshape (j : ℕ) : (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      mixedBridgeOldInverseBaseline M j *
      (13 * (5 / 10 ^ 24 : ℝ) * (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
        (3 : ℝ) ^ (6 * gammaZero * j))) =
      c * (((j : ℝ) + 1) ^ 2 * (inverseHistoryDiscount ^ (2 * j) *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)))) := by
    simp only [c, mixedBridgeOldInverseBaseline]
    ring
  have hnn (j : ℕ) : 0 ≤ c * (((j : ℝ) + 1) ^ 2 * (inverseHistoryDiscount ^ (2 * j) *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)))) := by
    apply mul_nonneg hc0
    apply mul_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  have hle (j : ℕ) : c * (((j : ℝ) + 1) ^ 2 * (inverseHistoryDiscount ^ (2 * j) *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)))) ≤
      c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdepthExp j) (sq_nonneg _)) hc0
  have hdom : Summable (fun j : ℕ => c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j)) :=
    hgeom.1.mul_left c
  have hsum : Summable (fun j : ℕ => c * (((j : ℝ) + 1) ^ 2 * (inverseHistoryDiscount ^ (2 * j) *
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) * (3 : ℝ) ^ (6 * gammaZero * (j : ℝ))))) :=
    Summable.of_nonneg_of_le hnn hle hdom
  simp_rw [hshape]
  refine ⟨hsum, ?_⟩
  have hR : (∑' j : ℕ, c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j)) = c * 1900 := by
    rw [tsum_mul_left, hgeom.2]
    norm_num
  have h1 := hsum.tsum_le_tsum hle hdom
  rw [hR] at h1
  have h2 : c * 1900 ≤ (1 / (4 * 10 ^ 12 : ℝ)) * theta M := by
    have hcoef0 : 0 ≤ (3683 / 2500 : ℝ) * (13 * (5 / 10 ^ 24 : ℝ)) * 1900 := by norm_num
    calc c * 1900 = theta M * ((1 - inverseHistoryDiscount ^ 2) *
            ((3683 / 2500 : ℝ) * (13 * (5 / 10 ^ 24 : ℝ)) * 1900) * (invTraceM : ℝ)) := by
          simp only [c]; ring
      _ ≤ theta M * (1 * ((3683 / 2500 : ℝ) * (13 * (5 / 10 ^ 24 : ℝ)) * 1900) * 10 ^ 6) := by
          apply mul_le_mul_of_nonneg_left _ htheta
          exact mul_le_mul (mul_le_mul_of_nonneg_right hΔ1 hcoef0) hcap hM0
            (by positivity)
      _ ≤ _ := by
          have : (1 * ((3683 / 2500 : ℝ) * (13 * (5 / 10 ^ 24 : ℝ)) * 1900) * 10 ^ 6) ≤
              1 / (4 * 10 ^ 12 : ℝ) := by norm_num
          calc _ ≤ theta M * (1 / (4 * 10 ^ 12 : ℝ)) := mul_le_mul_of_nonneg_left this htheta
            _ = _ := by ring
  exact h1.trans h2

/-- The local depth-bank rare payment (five times the depth reserve). -/
theorem local_numeric (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      ((14103 / 10000 : ℝ) ^ 2 * (5 * inverseBankDepthReserve .localInverse M j) *
        (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)))) ∧
    (∑' j : ℕ, (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      ((14103 / 10000 : ℝ) ^ 2 * (5 * inverseBankDepthReserve .localInverse M j) *
        (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)))) ≤
      (14103 / 10000 : ℝ) ^ 2 * (5 / (13 * 10 ^ 12 : ℝ)) * theta M := by
  have hs := old_signed_depth_rare_summable M hγ
  have hd := old_signed_directional_rare_delta M hγ
  have hΔ0 : 0 ≤ 1 - inverseHistoryDiscount ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le
      inverse_history_discount_range.2.le)
  have hshape (j : ℕ) : (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      ((14103 / 10000 : ℝ) ^ 2 * (5 * inverseBankDepthReserve .localInverse M j) *
        (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j))) =
      ((1 - inverseHistoryDiscount ^ 2) * (5 * (14103 / 10000 : ℝ) ^ 2)) *
        (inverseHistoryDiscount ^ (2 * j) * inverseBankDepthReserve .localInverse M j *
          (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j))) := by
    ring
  simp_rw [hshape]
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hβ : 0 ≤ (14103 / 10000 : ℝ) ^ 2 := by positivity
  calc ((1 - inverseHistoryDiscount ^ 2) * (5 * (14103 / 10000 : ℝ) ^ 2)) *
        (∑' j : ℕ, inverseHistoryDiscount ^ (2 * j) * inverseBankDepthReserve .localInverse M j *
          (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)))
      = (5 * (14103 / 10000 : ℝ) ^ 2 / 13) * (13 * (1 - inverseHistoryDiscount ^ 2) *
        (∑' j : ℕ, inverseHistoryDiscount ^ (2 * j) * inverseBankDepthReserve .localInverse M j *
          (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)))) := by
        ring
    _ ≤ (5 * (14103 / 10000 : ℝ) ^ 2 / 13) * ((1 / 10 ^ 12 : ℝ) * theta M) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

/-- The same payment is in fact below `β² θ / 10³⁰` (the actual reserve is `3·10⁻⁴⁶`). -/
theorem local_numeric_small (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) :
    (∑' j : ℕ, (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      ((14103 / 10000 : ℝ) ^ 2 * (5 * inverseBankDepthReserve .localInverse M j) *
        (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)))) ≤
      (14103 / 10000 : ℝ) ^ 2 * (1 / 10 ^ 30 : ℝ) * theta M := by
  have hd := old_signed_directional_rare_series_bound M hγ
  have htheta : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : (0 : ℝ) ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  have hcap : (invTraceM : ℝ) ≤ 10 ^ 6 := by exact_mod_cast invTrace_coefficient.2.1.le
  have hΔ0 : 0 ≤ 1 - inverseHistoryDiscount ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le
      inverse_history_discount_range.2.le)
  have hΔ1 : 1 - inverseHistoryDiscount ^ 2 ≤ 1 := sub_le_self _ (sq_nonneg _)
  have hshape (j : ℕ) : (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
      ((14103 / 10000 : ℝ) ^ 2 * (5 * inverseBankDepthReserve .localInverse M j) *
        (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j))) =
      ((1 - inverseHistoryDiscount ^ 2) * (5 * (14103 / 10000 : ℝ) ^ 2)) *
        (inverseHistoryDiscount ^ (2 * j) * inverseBankDepthReserve .localInverse M j *
          (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j))) := by
    ring
  simp_rw [hshape]
  rw [tsum_mul_left]
  have hres : (inverseBankReserve .localInverse : ℝ) = 3 / 10 ^ 46 := by
    norm_num [inverseBankReserve]
  rw [hres] at hd
  have h1 : (3 / 10 ^ 46 : ℝ) * theta M * (invTraceM : ℝ) * 1900 ≤
      (3 / 10 ^ 46 : ℝ) * theta M * 10 ^ 6 * 1900 := by
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hcap (by positivity)
  have hS0 : 0 ≤ ∑' j : ℕ, inverseHistoryDiscount ^ (2 * j) *
      inverseBankDepthReserve .localInverse M j *
        (theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)) := by
    apply tsum_nonneg
    intro j
    have hr : 0 ≤ inverseBankDepthReserve .localInverse M j := by
      unfold inverseBankDepthReserve inverseBankReserve bankDepthFrame; positivity
    have hα0 : 0 ≤ inverseHistoryDiscount := inverse_history_discount_range.1.le
    positivity
  have hS := hd.trans h1
  have hA : (1 - inverseHistoryDiscount ^ 2) * (5 * (14103 / 10000 : ℝ) ^ 2) ≤
      5 * (14103 / 10000 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (14103 / 10000 : ℝ)]
  calc _ ≤ (5 * (14103 / 10000 : ℝ) ^ 2) * ((3 / 10 ^ 46 : ℝ) * theta M * 10 ^ 6 * 1900) :=
        mul_le_mul hA hS hS0 (by positivity)
    _ ≤ _ := by
        have : (5 * (14103 / 10000 : ℝ) ^ 2) * ((3 / 10 ^ 46 : ℝ) * 10 ^ 6 * 1900) ≤
            (14103 / 10000 : ℝ) ^ 2 * (1 / 10 ^ 30 : ℝ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right this htheta]

end
end ASDExplicitGamma.Scalar
