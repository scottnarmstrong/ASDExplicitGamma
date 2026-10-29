module

public import ASDExplicitGamma.Cold.ColdHistoryChoiceTable
public import ASDExplicitGamma.Cold.ColdHistoryOldTable
public import ASDExplicitGamma.Cold.ColdScalingAlgebra
public import ASDExplicitGamma.Numerics.Cold.HistoryCertificate

/-! # Analytic soundness of the checked complete-history table -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Nonnegativity of each analytic depth cap used by the table. -/
theorem cold_history_table_depth_nonneg {j r : ℕ} (hj : j ≤ 128) (hr : r < j) :
    0 ≤ coldHistoryDepthCap (fun k => (coldMomentAt k:ℝ)) (fun k => (coldMeanAt k:ℝ)) j r := by
  unfold coldHistoryDepthCap
  apply le_min
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Rat.cast_nonneg.mpr (cold_table_nonneg _ (List.mem_range.mpr (by omega))).2)
  · apply Finset.le_inf' (coldHistoryEarlierLags_nonempty j r)
    intro k hk
    have hklt := coldHistoryEarlierLags_lt (by omega : 0 < j) hk
    have hs := cold_table_nonneg k (List.mem_range.mpr (by omega))
    exact add_nonneg (Rat.cast_nonneg.mpr hs.1) (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (coldCenteredMomentCap_nonneg (Rat.cast_nonneg.mpr hs.2) _))

/-- Every term in the actual finite prefix is bounded before outward addition. -/
theorem cold_history_prefix_table (j : ℕ) (hj : j ≤ 128) :
    (∑ r ∈ Finset.range j, coldHistoryAlpha^r*
      coldHistoryDepthCap (fun k => (coldMomentAt k:ℝ)) (fun k => (coldMeanAt k:ℝ)) j r) ≤
        (coldHistoryWeightedSum j:ℝ) := by
  have h := cold_le_up_sum_fold (List.range j)
    (fun r => coldHistoryAlpha^r*coldHistoryDepthCap (fun k => (coldMomentAt k:ℝ))
      (fun k => (coldMeanAt k:ℝ)) j r) (coldHistoryChoice j)
    (a := 0) (A := 0) (by norm_num) (fun r hr => cold_history_choice_table hj (List.mem_range.mp hr))
  rw [cold_range_list_sum,zero_add] at h
  exact h

/-- The full analytic history cap is bounded by the kernel-checked table.
The comparison includes the old branch and the complete fine beta^j S tail. -/
theorem cold_history_table_sound {j : ℕ} (hj : j ∈ coldUpdatedLags) :
    coldTriangularHistoryCap (fun k => (coldMomentAt k:ℝ)) (fun k => (coldMeanAt k:ℝ))
      (coldA:ℝ) (coldR20:ℝ) (coldS20:ℝ) j ≤ (coldHistoryAt j:ℝ) := by
  have hj128 : j ≤ 128 := (cold_updated_lag_bounds j hj).2
  rw [cold_history_table_check j hj]
  unfold coldTriangularHistoryCap coldHistoryExpected
  rw [Rat.cast_min,Rat.cast_min]
  apply min_le_min le_rfl
  apply min_le_min (cold_history_old_table j hj128)
  apply cold_up_add_mono
  · apply cold_up_mul_mono (sub_nonneg.mpr coldHistoryAlpha_le_one)
      (Finset.sum_nonneg fun r hr => mul_nonneg (pow_nonneg coldHistoryAlpha_pos.le _)
        (cold_history_table_depth_nonneg hj128 (Finset.mem_range.mp hr)))
      coldOneMinusAlpha_sound (cold_history_prefix_table j hj128)
  · exact cold_up_mul_mono (pow_nonneg coldHistoryBeta_pos.le _)
      (by norm_num [coldS20]) (cold_beta_power_table j hj128) (cold_round_up_real coldS20)

/-- Proportional source caps fit the same endpoint history table without rerounding it. -/
theorem cold_history_table_scaled {θ : ℝ} (hθ : 0 ≤ θ) {j : ℕ} (hj : j ∈ coldUpdatedLags) :
    coldTriangularHistoryCap (fun k => θ*(coldMomentAt k:ℝ)) (fun k => θ*(coldMeanAt k:ℝ))
      (θ*(coldA:ℝ)) (θ*(coldR20:ℝ)) (θ*(coldS20:ℝ)) j ≤ θ*(coldHistoryAt j:ℝ) := by
  rw [coldTriangularHistoryCap_scale hθ]
  exact mul_le_mul_of_nonneg_left (cold_history_table_sound hj) hθ

end ASDExplicitGamma.Cold
