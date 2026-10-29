module

public import ASDExplicitGamma.Cold.ColdOutwardSum
public import ASDExplicitGamma.Cold.ColdHistoryCaps

/-! # Soundness of the rounded old-history branch -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Each old-history cutoff term is dominated by its outward rational counterpart. -/
theorem cold_history_old_cutoff_table {j r : ℕ} (hj : j ≤ 128) (hr : r < j) :
    coldHistoryBeta^r*min 1 (4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ))) ≤
      (coldUpMul (coldBetaPowUpper r)
        (min 1 (coldRoundUp (2*coldSqrt19Upper*coldDecay (j-r)))):ℝ) := by
  have hdec : 0 ≤ (3:ℝ)^(-((j-r:ℕ):ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hcoef := mul_le_mul_of_nonneg_right cold_table_sqrt19_upper (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hdec)
  have hround := cold_round_up_real (2*coldSqrt19Upper*coldDecay (j-r))
  have hexact : 4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ)) ≤
      (2*coldSqrt19Upper*coldDecay (j-r):ℚ) := by
    push_cast
    rw [cold_table_decay]
    nlinarith only [hcoef]
  have hcut : min 1 (4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ))) ≤
      ((min 1 (coldRoundUp (2*coldSqrt19Upper*coldDecay (j-r))):ℚ):ℝ) := by
    rw [Rat.cast_min,Rat.cast_one]
    exact min_le_min le_rfl (hexact.trans hround)
  exact cold_up_mul_mono (pow_nonneg coldHistoryBeta_pos.le _) (by positivity)
    (cold_beta_power_table r (by omega)) hcut

/-- The old-history source expression, including all complete-tail mass, is bounded
by the exact outward rational expression. -/
theorem cold_history_old_table (j : ℕ) (hj : j ≤ 128) :
    coldOldHistoryCap (coldA:ℝ) (coldR20:ℝ) (coldS20:ℝ) j ≤ (coldHistoryOldTerm j:ℝ) := by
  have ha : 0 ≤ (coldA:ℝ) := by norm_num [coldA]
  have hR : 0 ≤ (coldR20:ℝ) := by norm_num [coldR20]
  have hS : 0 ≤ (coldS20:ℝ) := by norm_num [coldS20]
  have hα : 0 ≤ 1-coldHistoryAlpha := sub_nonneg.mpr coldHistoryAlpha_le_one
  have hαj : 0 ≤ 1-coldHistoryAlpha^j := sub_nonneg.mpr
    (pow_le_one₀ coldHistoryAlpha_pos.le coldHistoryAlpha_le_one)
  let sumQ := coldListSum (List.range j) (fun r => coldUpMul (coldBetaPowUpper r)
    (min 1 (coldRoundUp (2*coldSqrt19Upper*coldDecay (j-r)))))
  let sumR := ∑ r ∈ Finset.range j, coldHistoryBeta^r*
    min 1 (4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ)))
  have hsum0 : 0 ≤ sumR := Finset.sum_nonneg (fun r _ =>
    mul_nonneg (pow_nonneg coldHistoryBeta_pos.le _) (le_min (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) _))))
  have hsum : sumR ≤ (sumQ:ℝ) := by
    rw [show (sumQ:ℝ) = ∑ r ∈ Finset.range j,
      (coldUpMul (coldBetaPowUpper r) (min 1 (coldRoundUp (2*coldSqrt19Upper*coldDecay (j-r)))):ℝ)
      from cold_list_sum_range_cast _ _]
    exact Finset.sum_le_sum (fun r hr => cold_history_old_cutoff_table hj (Finset.mem_range.mp hr))
  have hA : (1-coldHistoryAlpha^j)*(coldA:ℝ) ≤
      (coldUpMul (coldRoundUp coldA) (coldRoundUp (1-coldAlphaPowLower j)):ℝ) := by
    rw [mul_comm]
    apply cold_up_mul_mono ha hαj (cold_round_up_real _)
    have h := (cold_alpha_power_table j hj).1
    have hround := cold_round_up_real (1-coldAlphaPowLower j)
    push_cast at hround
    exact (sub_le_sub_left h 1).trans hround
  have hBR : (1-coldHistoryAlpha)*(coldR20:ℝ) ≤
      (coldUpMul coldOneMinusAlphaUpper (coldRoundUp coldR20):ℝ) :=
    cold_up_mul_mono hα hR coldOneMinusAlpha_sound (cold_round_up_real _)
  have hB := cold_up_mul_mono (mul_nonneg hα hR) hsum0 hBR hsum
  have htail := cold_up_mul_mono (pow_nonneg coldHistoryBeta_pos.le _) hS
    (cold_beta_power_table j hj) (cold_round_up_real coldS20)
  have h := cold_up_add_mono (cold_up_add_mono hA hB) htail
  exact h

end ASDExplicitGamma.Cold
