module

public import ASDExplicitGamma.Cold.ColdRoundingAlgebra

/-! # Soundness of every finite history depth-table choice -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Alpha times the finite-union population factor gives exactly beta at every depth. -/
theorem cold_history_population_weight (r : ℕ) :
    coldHistoryAlpha^r*(9:ℝ)^((r:ℝ)/20) = coldHistoryBeta^r := by
  rw [← coldHistoryUnionFactor_pow,← mul_pow,cold_history_weight_relation]

/-- Each weighted analytic depth cap is dominated by the table's entire minimum fold. -/
theorem cold_history_choice_table {j r : ℕ} (hj : j ≤ 128) (hr : r < j) :
    coldHistoryAlpha^r*coldHistoryDepthCap (fun k => (coldMomentAt k:ℝ))
      (fun k => (coldMeanAt k:ℝ)) j r ≤ (coldHistoryChoice j r:ℝ) := by
  let M := fun k => (coldMomentAt k:ℝ)
  let D := fun k => (coldMeanAt k:ℝ)
  let C := coldHistoryDepthCap M D j r
  have hr128 : r ≤ 128 := by omega
  have hell : j-r ≤ 128 := by omega
  have hM : 0 ≤ M (j-r) := Rat.cast_nonneg.mpr
    (cold_table_nonneg _ (List.mem_range.mpr (by omega))).2
  have hα : 0 ≤ coldHistoryAlpha^r := pow_nonneg coldHistoryAlpha_pos.le _
  have hβ : 0 ≤ coldHistoryBeta^r := pow_nonneg coldHistoryBeta_pos.le _
  have hraw : coldHistoryAlpha^r*C ≤
      (coldUpMul (coldBetaPowUpper r) (coldRoundUp (coldMomentAt (j-r))):ℝ) := by
    have hc : C ≤ (9:ℝ)^((r:ℝ)/20)*M (j-r) := min_le_left _ _
    calc
      _ ≤ coldHistoryAlpha^r*((9:ℝ)^((r:ℝ)/20)*M (j-r)) := mul_le_mul_of_nonneg_left hc hα
      _ = coldHistoryBeta^r*M (j-r) := by rw [← mul_assoc,cold_history_population_weight]
      _ ≤ _ := cold_up_mul_mono hβ hM (cold_beta_power_table r hr128)
        (cold_round_up_real (coldMomentAt (j-r)))
  unfold coldHistoryChoice
  apply cold_le_fold_min _ _ hraw
  intro k hk
  have hk' : k ∈ coldHistoryEarlierLags j r := hk
  have hk128 : k ≤ 128 := by
    have hh := coldHistoryEarlierLags_lt (by omega : 0 < j) hk'
    omega
  have hsign := cold_table_nonneg k (List.mem_range.mpr (by omega))
  have hD : 0 ≤ D k := Rat.cast_nonneg.mpr hsign.1
  have hE : 0 ≤ coldCenteredMomentCap (M k) (j-r-k) :=
    coldCenteredMomentCap_nonneg (Rat.cast_nonneg.mpr hsign.2) _
  have hc : C ≤ D k+(9:ℝ)^((r:ℝ)/20)*coldCenteredMomentCap (M k) (j-r-k) :=
    (min_le_right _ _).trans (Finset.inf'_le _ hk')
  have he := cold_centered_cap_le_history k (j-r-k) hk128
  have htransport : coldHistoryAlpha^r*C ≤
      coldHistoryAlpha^r*D k+coldHistoryBeta^r*coldCenteredMomentCap (M k) (j-r-k) := by
    have hh := mul_le_mul_of_nonneg_left hc hα
    rw [mul_add,← mul_assoc,cold_history_population_weight] at hh
    exact hh
  apply htransport.trans
  apply cold_up_add_mono
  · exact cold_up_mul_mono hα hD (cold_alpha_power_table r hr128).2
      (cold_round_up_real (coldMeanAt k))
  · exact cold_up_mul_mono hβ hE (cold_beta_power_table r hr128)
      (he.trans (cold_round_up_real (coldHistoryE k (j-r-k))))

end ASDExplicitGamma.Cold
